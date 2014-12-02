{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, UndecidableInstances, TupleSections, OverloadedStrings #-}
module Language.Haskell.Liquid.PredType (
    PrType
  , TyConP (..), DataConP (..)
  , dataConTy
  , dataConPSpecType
  , makeTyConInfo
--   , unify -- TODO: remove this!
  , replacePreds

  , replacePredsWithRefs
  , pVartoRConc

  -- * Dummy `Type` that represents _all_ abstract-predicates
  , predType

  -- * Compute @RType@ of a given @PVar@
  , pvarRType
    
  , substParg
  , pApp
  , wiredSortedSyms
  ) where

-- import PprCore          (pprCoreExpr)
import Id               (idType)
import CoreSyn  hiding (collectArgs)
import Type
import TypeRep
import qualified TyCon as TC
import Literal
import Coercion         (coercionType, coercionKind)
import Pair             (pSnd)
import FastString       (sLit)
import qualified Outputable as O
import Text.PrettyPrint.HughesPJ
import DataCon

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import Data.List        (partition, foldl')
import Data.Monoid      (mempty, mappend)
import qualified Data.Text as T

import Language.Fixpoint.Misc
import Language.Fixpoint.Types hiding (Predicate, Expr)
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Types 
import Language.Haskell.Liquid.RefType  hiding (generalize)
import Language.Haskell.Liquid.GhcMisc
import Language.Haskell.Liquid.Misc

import Control.Applicative  ((<$>), (<*>))
import Control.Monad.State
import Data.List (nub)

import Data.Default

import Debug.Trace (trace)

makeTyConInfo = hashMapMapWithKey mkRTyCon . M.fromList

mkRTyCon ::  TC.TyCon -> TyConP -> RTyCon
mkRTyCon tc (TyConP αs' ps ls tyvariance predvariance size) = RTyCon tc pvs' (mkTyConInfo tc tyvariance predvariance size)
  where τs   = [rVar α :: RSort |  α <- TC.tyConTyVars tc]
        pvs' = subts (zip αs' τs) <$> ps

dataConPSpecType :: DataCon -> DataConP -> SpecType 
dataConPSpecType dc (DataConP _ vs ps ls cs yts rt) = mkArrow vs ps ls ts' rt'
  where 
    (xs, ts) = unzip $ reverse yts
    mkDSym   = (`mappend` symbol dc) . (`mappend` "_") . symbol
    ys       = mkDSym <$> xs
    tx _  []     []     []     = []
    tx su (x:xs) (y:ys) (t:ts) = (y, subst (F.mkSubst su) t)
                               : tx ((x, F.EVar y):su) xs ys ts
    yts'     = tx [] xs ys ts
    ts'      = map ("" ,) cs ++ yts'
    su       = F.mkSubst [(x, F.EVar y) | (x, y) <- zip xs ys]
    rt'      = subst su rt

instance PPrint TyConP where
  pprint (TyConP vs ps ls _ _ _) 
    = (parens $ hsep (punctuate comma (map pprint vs))) <+>
      (parens $ hsep (punctuate comma (map pprint ps))) <+>
      (parens $ hsep (punctuate comma (map pprint ls)))

instance Show TyConP where
 show = showpp -- showSDoc . ppr

instance PPrint DataConP where
  pprint (DataConP _ vs ps ls cs yts t)
     = (parens $ hsep (punctuate comma (map pprint vs))) <+>
       (parens $ hsep (punctuate comma (map pprint ps))) <+>
       (parens $ hsep (punctuate comma (map pprint ls))) <+>
       (parens $ hsep (punctuate comma (map pprint cs))) <+>
       (parens $ hsep (punctuate comma (map pprint yts))) <+>
       pprint t

instance Show DataConP where
  show = showpp

dataConTy m (TyVarTy v)            
  = M.lookupDefault (rVar v) (RTV v) m
dataConTy m (FunTy t1 t2)          
  = rFun dummySymbol (dataConTy m t1) (dataConTy m t2)
dataConTy m (ForAllTy α t)          
  = RAllT (rTyVar α) (dataConTy m t)
dataConTy m (TyConApp c ts)        
  = rApp c (dataConTy m <$> ts) [] mempty
dataConTy _ _
  = error "ofTypePAppTy"

---------------------------------------------------------------------------
-- | Unify PrType with SpecType -------------------------------------------
---------------------------------------------------------------------------
unify               :: Maybe PrType -> SpecType -> SpecType 
---------------------------------------------------------------------------
unify (Just pt) rt  = evalState (unifyS rt pt) S.empty
unify _         t   = t

---------------------------------------------------------------------------
unifyS :: SpecType -> PrType -> State (S.HashSet UsedPVar) SpecType 
---------------------------------------------------------------------------

unifyS (RAllS s t) pt
  = do t' <- unifyS t pt 
       return $ RAllS s t'

unifyS t (RAllS s pt) 
  = do t' <- unifyS t pt 
       return $ RAllS s t'

unifyS (RAllP p t) pt
  = do t' <- unifyS t pt 
       s  <- get
       put $ S.delete (uPVar p) s
       return $ RAllP p t' 
--        if (uPVar p `S.member` s) then return $ RAllP p t' else return t'

unifyS t (RAllP p pt)
  = do t' <- unifyS t pt 
       s  <- get
       put $ S.delete (uPVar p) s
       if (uPVar p `S.member` s) then return $ RAllP p t' else return t'

unifyS (RAllT (v@(RTV α)) t) (RAllT v' pt) 
  = do t'    <- unifyS t $ subsTyVar_meet (v', (rVar α) :: RSort, RVar v mempty) pt 
       return $ RAllT v t'

unifyS (RFun x rt1 rt2 _) (RFun x' pt1 pt2 _)
  = do t1' <- unifyS rt1 pt1
       t2' <- unifyS rt2 $ substParg (x', EVar x) pt2
       return $ rFun x t1' t2' 

unifyS (RAppTy rt1 rt2 r) (RAppTy pt1 pt2 p)
  = do t1' <- unifyS rt1 pt1
       t2' <- unifyS rt2 pt2
       return $ RAppTy t1' t2' (bUnify r p)

unifyS (RVar v a) (RVar _ p)
  = do modify $ \s -> s `S.union` (S.fromList $ pvars p)
       return $ RVar v $ bUnify a p

unifyS (RApp c ts rs r) (RApp _ pts ps p)
  = do modify $ \s -> s `S.union` fm
       ts'   <- zipWithM unifyS ts pts
       return $ RApp c ts' rs (bUnify r p)
    where 
       fm       = S.fromList $ concatMap pvars (p:fps) 
       fps      = getR <$> ps
       getR (RPropP _ r) = r
       getR (RProp _ _ ) = mempty 

unifyS (RAllE x tx t) (RAllE x' tx' t') | x == x'
  = RAllE x <$> unifyS tx tx' <*> unifyS t t'

unifyS (REx x tx t) (REx x' tx' t') | x == x'
  = REx x   <$> unifyS tx tx' <*> unifyS t t'
    
unifyS t (REx x' tx' t')
  = REx x' ((\p -> U mempty p mempty) <$> tx') <$> unifyS t t'
    
unifyS t@(RVar v a) (RAllE x' tx' t')
  = RAllE x' ((\p -> U mempty p mempty)<$> tx') <$> (unifyS t t')

unifyS t1 t2                
  = error ("unifyS" ++ show t1 ++ " with " ++ show t2)

-- pToReft p = Reft (vv, [RPvar p]) 
pToReft  = (\p -> U mempty p mempty) . pdVar 

bUnify r (Pr pvs)              = foldl' meet r $ pToReft <$> pvs
                                 
-- ORIG unifyRef (RPropP s r) p        = RPropP s $ bUnify r p -- (foldl' meet r      $ pToReft <$> pvs)
-- ORIG unifyRef (RProp s t) (Pr pvs)  = RProp s  $ foldl' strengthen t $ pToReft <$> pvs

-- ORIG zipWithZero f xz yz  = go
-- ORIG   where
-- ORIG     go []     ys     = (xz `f`) <$> ys
-- ORIG     go xs     []     = (`f` yz) <$> xs
-- ORIG     go (x:xs) (y:ys) = f x y  : go xs ys
    
-- ORIG zipWithZero _ _  _  []     []     = []
-- ORIG zipWithZero f xz yz []     (y:ys) = f xz y : zipWithZero f xz yz [] ys
-- ORIG zipWithZero f xz yz (x:xs) []     = f x yz : zipWithZero f xz yz xs []
-- ORIG zipWithZero f xz yz (x:xs) (y:ys) = f x y  : zipWithZero f xz yz xs ys
 
----------------------------------------------------------------------------
----- Interface: Replace Predicate With Uninterprented Function Symbol -----
----------------------------------------------------------------------------

replacePredsWithRefs (p, r) (U (Reft(v, rs)) (Pr ps) s) 
  = U (Reft (v, rs ++ rs')) (Pr ps2) s
  where rs'              = r . (v,) . pargs <$> ps1
        (ps1, ps2)       = partition (==p) ps
        freeSymbols      = snd3 <$> filter (\(_, x, y) -> EVar x == y) pargs1
        pargs1           = concatMap pargs ps1

pVartoRConc p (v, args) | length args == length (pargs p) 
  = RConc $ pApp (pname p) $ EVar v:(thd3 <$> args)

pVartoRConc p (v, args)
  = RConc $ pApp (pname p) $ EVar v : args'
  where args' = (thd3 <$> args) ++ (drop (length args) (thd3 <$> pargs p))

-----------------------------------------------------------------------
-- | @pvarRType π@ returns a trivial @RType@ corresponding to the
--   function signature for a @PVar@ @π@. For example, if
--      @π :: T1 -> T2 -> T3 -> Prop@
--   then @pvarRType π@ returns an @RType@ with an @RTycon@ called
--   @predRTyCon@ `RApp predRTyCon [T1, T2, T3]` 
-----------------------------------------------------------------------
pvarRType :: (PPrint r, Reftable r) => PVar RSort -> RRType r
-----------------------------------------------------------------------
pvarRType (PV _ k {- (PVProp τ) -} _ args) = rpredType k (fst3 <$> args) -- (ty:tys)
  -- where
  --   ty  = uRTypeGen τ 
  --   tys = uRTypeGen . fst3 <$> args
        

-- rpredType    :: (PPrint r, Reftable r) => PVKind (RRType r) -> [RRType r] -> RRType r
rpredType (PVProp t) ts = RApp predRTyCon  (uRTypeGen <$> t : ts) [] mempty
rpredType PVHProp    ts = RApp wpredRTyCon (uRTypeGen <$>     ts) [] mempty  

predRTyCon   :: RTyCon
predRTyCon   = symbolRTyCon predName

wpredRTyCon   :: RTyCon
wpredRTyCon   = symbolRTyCon wpredName

symbolRTyCon   :: Symbol -> RTyCon
symbolRTyCon n = RTyCon (stringTyCon 'x' 42 $ symbolString n) [] def

-------------------------------------------------------------------------------------
-- | Instantiate `PVar` with `RTProp` -----------------------------------------------
-------------------------------------------------------------------------------------
-- | @replacePreds@ is the main function used to substitute an (abstract)
--   predicate with a concrete Ref, that is either an `RProp` or `RHProp`
--   type. The substitution is invoked to obtain the `SpecType` resulting
--   at /predicate application/ sites in 'Language.Haskell.Liquid.Constraint'.
--   The range of the `PVar` substitutions are /fresh/ or /true/ `RefType`. 
--   That is, there are no further _quantified_ `PVar` in the target.
-------------------------------------------------------------------------------------
replacePreds                 :: String -> SpecType -> [(RPVar, SpecProp)] -> SpecType 
-------------------------------------------------------------------------------------
replacePreds msg             = foldl' go 
  where
    go z (π, t@(RProp _ _)) = substPred msg   (π, t)     z
    go _ (_, RPropP _ _)    = error "replacePreds on RPropP"
    go _ (_, RHProp _ _)    = errorstar "TODO:EFFECTS:replacePreds"

-- TODO: replace `replacePreds` with
-- instance SubsTy RPVar (Ref RReft SpecType) SpecType where
--   subt (pv, r) t = replacePreds "replacePred" t (pv, r)

-- replacePreds :: String -> SpecType -> [(RPVar, Ref Reft RefType)] -> SpecType 
-- replacePreds msg       = foldl' go 
--   where go z (π, RProp t) = substPred msg   (π, t)     z
--         go z (π, RPropP r) = replacePVarReft (π, r) <$> z

-------------------------------------------------------------------------------
substPred :: String -> (RPVar, SpecProp) -> SpecType -> SpecType
-------------------------------------------------------------------------------

substPred _   (π, RProp ss (RVar a1 r1)) t@(RVar a2 r2)
  | isPredInReft && a1 == a2    = RVar a1 $ meetListWithPSubs πs ss r1 r2'
  | isPredInReft                = errorstar ("substPred RVar Var Mismatch" ++ show (a1, a2))
  | otherwise                   = t
  where
    (r2', πs)                   = splitRPvar π r2
    isPredInReft                = not $ null πs 

substPred msg su@(π, _ ) (RApp c ts rs r)
  | null πs                     = t' 
  | otherwise                   = substRCon msg su t' πs r2'
  where
    t'                          = RApp c (substPred msg su <$> ts) (substPredP msg su <$> rs) r
    (r2', πs)                   = splitRPvar π r

substPred msg (p, tp) (RAllP (q@(PV _ _ _ _)) t)
  | p /= q                      = RAllP q $ substPred msg (p, tp) t
  | otherwise                   = RAllP q t 

substPred msg su (RAllT a t)    = RAllT a (substPred msg su t)

substPred msg su@(π,_ ) (RFun x t t' r) 
  | null πs                     = RFun x (substPred msg su t) (substPred msg su t') r
  | otherwise                   = {-meetListWithPSubs πs πt -}(RFun x t t' r')
  where (r', πs)                = splitRPvar π r

substPred msg su (RRTy e r o t) = RRTy (mapSnd (substPred msg su) <$> e) r o (substPred msg su t)
substPred msg su (RAllE x t t') = RAllE x (substPred msg su t) (substPred msg su t')
substPred msg su (REx x t t')   = REx   x (substPred msg su t) (substPred msg su t')
substPred _   _  t              = t

-- | Requires: @not $ null πs@
-- substRCon :: String -> (RPVar, SpecType) -> SpecType -> SpecType

substRCon msg (_, RProp ss (RApp c1 ts1 rs1 r1)) (RApp c2 ts2 rs2 _) πs r2'
  | rtc_tc c1 == rtc_tc c2 = RApp c1 ts rs $ meetListWithPSubs πs ss r1 r2'
  where
    ts                     = safeZipWith (msg ++ ": substRCon")  strSub  ts1  ts2
    rs                     = safeZipWith (msg ++ ": substRCon2") strSubR rs1' rs2'
    -- TODO: REMOVE `pad` just use rs2 ?
    (rs1', rs2')           = pad "substRCon" top rs1 rs2
    strSub r1 r2           = meetListWithPSubs πs ss r1 r2
    strSubR r1 r2          = meetListWithPSubsRef πs ss r1 r2



substRCon msg su t _ _        = errorstar $ msg ++ " substRCon " ++ showpp (su, t)

substPredP msg su@(p, RProp ss tt) (RProp s t)       
  = RProp ss' $ substPred (msg ++ ": substPredP") su t
 where
   ss' = drop n ss ++  s
   n   = length ss - length (freeArgsPs p t)

substPredP _ _  (RHProp _ _)       
  = errorstar "TODO:EFFECTS:substPredP"

substPredP _ _  (RPropP _ _)       
  = error $ "RPropP found in substPredP"




splitRPvar pv (U x (Pr pvs) s) = (U x (Pr pvs') s, epvs)
  where
    (epvs, pvs')               = partition (uPVar pv ==) pvs


isPredInType p (RVar _ r) 
  = isPredInURef p r
isPredInType p (RFun _ t1 t2 r) 
  = isPredInURef p r || isPredInType p t1 || isPredInType p t2
isPredInType p (RAllT _ t)
  = isPredInType p t 
isPredInType p (RAllP p' t)
  = not (p == p') && isPredInType p t 
isPredInType p (RApp _ ts _ r) 
  = isPredInURef p r || any (isPredInType p) ts
isPredInType p (RAllE _ t1 t2) 
  = isPredInType p t1 || isPredInType p t2 
isPredInType p (RAppTy t1 t2 r) 
  = isPredInURef p r || isPredInType p t1 || isPredInType p t2
isPredInType _ (RExprArg _)              
  = False
isPredInType _ (ROth _)
  = False

isPredInURef p (U _ (Pr ps) _) = any (uPVar p ==) ps

freeArgsPs p (RVar _ r) 
  = freeArgsPsRef p r
freeArgsPs p (RFun _ t1 t2 r) 
  = nub $  freeArgsPsRef p r ++ freeArgsPs p t1 ++ freeArgsPs p t2
freeArgsPs p (RAllT _ t)
  = freeArgsPs p t 
freeArgsPs p (RAllP p' t)
  | p == p'   = []
  | otherwise = freeArgsPs p t 
freeArgsPs p (RApp _ ts _ r) 
  = nub $ freeArgsPsRef p r ++ concatMap (freeArgsPs p) ts
freeArgsPs p (RAllE _ t1 t2) 
  = nub $ freeArgsPs p t1 ++ freeArgsPs p t2 
freeArgsPs p (RAppTy t1 t2 r) 
  = nub $ freeArgsPsRef p r ++ freeArgsPs p t1 ++ freeArgsPs p t2
freeArgsPs _ (RExprArg _)              
  = []
freeArgsPs _ (ROth _)
  = []

freeArgsPsRef p (U _ (Pr ps) _) = [x | (_, x, w) <- (concatMap pargs ps'),  (EVar x) == w]
  where 
   ps' = f <$> filter (uPVar p ==) ps
   f q = q {pargs = pargs q ++ drop (length (pargs q)) (pargs $ uPVar p)}

meetListWithPSubs πs ss r1 r2    = foldl' (meetListWithPSub ss r1) r2 πs
meetListWithPSubsRef πs ss r1 r2 = foldl' ((meetListWithPSubRef ss) r1) r2 πs

meetListWithPSub ::  (Reftable r, PPrint t) => [(Symbol, RSort)]-> r -> r -> PVar t -> r
meetListWithPSub ss r1 r2 π
  | all (\(_, x, EVar y) -> x == y) (pargs π)
  = r2 `meet` r1
  | all (\(_, x, EVar y) -> x /= y) (pargs π)
  = r2 `meet` (subst su r1)
  | otherwise
  = errorstar $ "PredType.meetListWithPSub partial application to " ++ showpp π
  where su  = mkSubst [(x, y) | (x, (_, _, y)) <- zip (fst <$> ss) (pargs π)]

meetListWithPSubRef ss (RProp s1 r1) (RProp s2 r2) π
  | all (\(_, x, EVar y) -> x == y) (pargs π)
  = RProp s1 $ r2 `meet` r1      
  | all (\(_, x, EVar y) -> x /= y) (pargs π)
  = RProp s2 $ r2 `meet` (subst su r1)
  | otherwise
  = errorstar $ "PredType.meetListWithPSubRef partial application to " ++ showpp π
  where su  = mkSubst [(x, y) | (x, (_, _, y)) <- zip (fst <$> ss) (pargs π)]


----------------------------------------------------------------------------
-- | Interface: Modified CoreSyn.exprType due to predApp -------------------
----------------------------------------------------------------------------
predType   :: Type 
predType   = symbolType predName

wpredName, predName   :: Symbol
predName   = "Pred"
wpredName  = "WPred"

symbolType = TyVarTy . symbolTyVar 

-- | A more efficient version of 'applyTypeToArg' when we have several arguments.
--   The first argument is just for debugging, and gives some context
--   RJ: This function is UGLY. Two nested levels of where is a BAD idea.
--   Please fix.

applyTypeToArgs :: CoreExpr -> Type -> [CoreExpr] -> Type

applyTypeToArgs _ op_ty [] = op_ty

applyTypeToArgs e op_ty (Type ty : args)
  = -- Accumulate type arguments so we can instantiate all at once
    go [ty] args
  where
    go rev_tys (Type ty : args) = go (ty:rev_tys) args
    go rev_tys rest_args        = applyTypeToArgs e op_ty' rest_args
                                  where
                                    op_ty' = applyTysD msg op_ty (reverse rev_tys)
                                    msg    = O.text ("MYapplyTypeToArgs: " ++ panic_msg e op_ty)


applyTypeToArgs e op_ty (_ : args)
  = case (splitFunTy_maybe op_ty) of
        Just (_, res_ty) -> applyTypeToArgs e res_ty args
        Nothing          -> errorstar $ "MYapplyTypeToArgs" ++ panic_msg e op_ty

panic_msg :: CoreExpr -> Type -> String 
panic_msg e op_ty = showPpr e ++ " :: " ++ showPpr op_ty

substParg :: Functor f => (Symbol, F.Expr) -> f Predicate -> f Predicate
substParg (x, y) = fmap fp
  where
    fxy s        = if (s == EVar x) then y else s
    fp           = subvPredicate (\pv -> pv { pargs = mapThd3 fxy <$> pargs pv })

-------------------------------------------------------------------------------
-----------------------------  Predicate Application --------------------------
-------------------------------------------------------------------------------

pappArity  = 7

-- pappSym n  = S $ "papp" ++ show n

pappSort n = FFunc (2 * n) $ [ptycon] ++ args ++ [bSort]
  where ptycon = fApp (Left predFTyCon) $ FVar <$> [0..n-1]
        args   = FVar <$> [n..(2*n-1)]
        bSort  = FApp boolFTyCon []
 
wiredSortedSyms = [(pappSym n, pappSort n) | n <- [1..pappArity]]

predFTyCon = symbolFTycon $ dummyLoc predName

-- pApp :: Symbol -> [F.Expr] -> Pred
-- pApp p es= PBexp $ EApp (dummyLoc $ pappSym $ length es) (EVar p:es)

