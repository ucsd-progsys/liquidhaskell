{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, UndecidableInstances, TupleSections #-}
module Language.Haskell.Liquid.PredType (
    PrType
  , TyConP (..), DataConP (..)
  , dataConTy, dataConPSpecType, makeTyConInfo
  , unify, replacePreds, exprType, predType
  , replacePredsWithRefs, pVartoRConc, toPredType
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
import Data.Monoid      (mempty)

import Language.Fixpoint.Misc
import Language.Fixpoint.Types hiding (Predicate, Expr)
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Types 
import Language.Haskell.Liquid.RefType  hiding (generalize)
import Language.Haskell.Liquid.GhcMisc

import Control.Applicative  ((<$>))
import Control.Monad.State

makeTyConInfo = hashMapMapWithKey mkRTyCon . M.fromList

mkRTyCon ::  TC.TyCon -> TyConP -> RTyCon
mkRTyCon tc (TyConP αs' ps cv conv size) = RTyCon tc pvs' (mkTyConInfo tc cv conv size)
  where τs   = [rVar α :: RSort |  α <- TC.tyConTyVars tc]
        pvs' = subts (zip αs' τs) <$> ps

dataConPSpecType :: DataCon -> DataConP -> SpecType 
dataConPSpecType dc (DataConP vs ps cs yts rt) = mkArrow vs ps ts' rt'
  where (xs, ts) = unzip $ reverse yts
        ys       = mkDSym <$> xs
        su       = F.mkSubst [(x, F.EVar y) | (x, y) <- zip xs ys]
        rt'      = subst su rt
        mkDSym   = stringSymbol . (++ ('_':(showPpr dc))) . show
        ts'      = map (S "",) cs ++ yts'
        tx _  []     []     []     = []
        tx su (x:xs) (y:ys) (t:ts) = (y, subst (F.mkSubst su) t)
                                   : tx ((x, F.EVar y):su) xs ys ts
        -- yts'     = zip ys (subst su <$> ts)
        yts'     = tx [] xs ys ts
--   where t1 = foldl' (\t2 (x, t1) -> rFun x t1 t2) rt yts
--         t2 = foldr RAllP t1 ps
--         t3 = foldr RAllT t2 vs


instance PPrint TyConP where
  pprint (TyConP vs ps _ _ _) 
    = (parens $ hsep (punctuate comma (map pprint vs))) <+>
      (parens $ hsep (punctuate comma (map pprint ps)))

instance Show TyConP where
 show = showpp -- showSDoc . ppr

instance PPrint DataConP where
  pprint (DataConP vs ps cs yts t)
     = (parens $ hsep (punctuate comma (map pprint vs))) <+>
       (parens $ hsep (punctuate comma (map pprint ps))) <+>
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
dataConTy _ t
  | Just t' <- ofPredTree (classifyPredType t)
  = t'
dataConTy m (TyConApp c ts)        
  = rApp c (dataConTy m <$> ts) [] mempty
dataConTy _ _
  = error "ofTypePAppTy"

---------------------------------------------------------------------------
-------------- Interfacing Between Predicates and Refinements -------------
---------------------------------------------------------------------------

---------------------------------------------------------------------------
--------------Interfacing: Unify PrType with SpecType ---------------------
---------------------------------------------------------------------------

unify :: Maybe PrType -> SpecType -> SpecType 
unify (Just pt) rt  = evalState (unifyS rt pt) S.empty
unify _         t   = t

---------------------------------------------------------------------------
unifyS :: SpecType -> PrType -> State (S.HashSet UsedPVar) SpecType 
---------------------------------------------------------------------------

unifyS (RAllP p t) pt
  = do t' <- unifyS t pt 
       s  <- get
       put $ S.delete (uPVar p) s
       if (uPVar p `S.member` s) then return $ RAllP p t' else return t'

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
       t2' <- unifyS rt2 (substParg (x', EVar x) pt2)
       return $ rFun x t1' t2' 

unifyS (RAppTy rt1 rt2 r) (RAppTy pt1 pt2 p)
  = do t1' <- unifyS rt1 pt1
       t2' <- unifyS rt2 pt2
       return $ RAppTy t1' t2' (bUnify r p)

unifyS t@(RCls _ _) (RCls _ _)
  = return t

unifyS (RVar v a) (RVar _ p)
  = do modify $ \s -> s `S.union` (S.fromList $ pvars p) -- (filter (/= PdTrue) [p]))
       return $ RVar v $ bUnify a p

unifyS (RApp c ts rs r) (RApp _ pts ps p)
  = do modify $ \s -> s `S.union` fm
       ts'   <- zipWithM unifyS ts pts
       return $ RApp c ts' rs' (bUnify r p)
    where 
       fm       = S.fromList $ concatMap pvars (fp:fps) 
       fp : fps = p : (getR <$> ps)
       rs'      = zipWithZero unifyRef (RMono [] top {- trueReft -}) mempty rs fps
       getR (RMono _ r) = r
       getR (RPoly _ _) = top 

unifyS (RAllE x tx t) (RAllE x' tx' t') | x == x'
  = liftM2 (RAllE x) (unifyS tx tx') (unifyS t t')

unifyS (REx x tx t) (REx x' tx' t') | x == x'
  = liftM2 (REx x) (unifyS tx tx') (unifyS t t')

unifyS t (REx x' tx' t')
  = liftM (REx x' (U top <$> tx')) (unifyS t t')

unifyS t@(RVar v a) (RAllE x' tx' t')
  = liftM (RAllE x' (U top <$> tx')) (unifyS t t')

unifyS t1 t2                
  = error ("unifyS" ++ show t1 ++ " with " ++ show t2)

bUnify a (Pr pvs)        = foldl' meet a $ pToReft <$> pvs

unifyRef (RMono s a) (Pr pvs) = RMono s $ foldl' meet a $ pToReft <$> pvs
unifyRef (RPoly s a) (Pr pvs) = RPoly s $ foldl' strengthen a $ pToReft <$> pvs

zipWithZero _ _  _  []     []     = []
zipWithZero f xz yz []     (y:ys) = (f xz y):(zipWithZero f xz yz [] ys)
zipWithZero f xz yz (x:xs) []     = (f x yz):(zipWithZero f xz yz xs [])
zipWithZero f xz yz (x:xs) (y:ys) = (f x y) :(zipWithZero f xz yz xs ys)
 
-- pToReft p = Reft (vv, [RPvar p]) 
pToReft = U top . pdVar 

----------------------------------------------------------------------------
----- Interface: Replace Predicate With Uninterprented Function Symbol -----
----------------------------------------------------------------------------

replacePredsWithRefs (p, r) (U (Reft(v, rs)) (Pr ps)) 
  = U (Reft (v, rs ++ rs')) (Pr ps2)
  where rs'              = r . (v,) . pargs <$> ps1
        (ps1, ps2)       = partition (==p) ps
        freeSymbols      = snd3 <$> filter (\(_, x, y) -> EVar x == y) pargs1
        pargs1           = concatMap pargs ps1

pVartoRConc p (v, args)
  = RConc $ pApp (pname p) $ EVar v:(thd3 <$> args)

toPredType (PV _ ptype args) = rpredType (ty:tys)
  where ty = uRTypeGen ptype
        tys = uRTypeGen . fst3 <$> args
        

----------------------------------------------------------------------------
---------- Interface: Replace Predicate With Type  -------------------------
----------------------------------------------------------------------------

-- | This is the main function used to substitute an (abstract) predicate
-- with a concrete Ref, of a compound (`RPoly`) type. The substitution is 
-- invoked to obtain the `SpecType` resulting at /predicate application/ 
-- sites in 'Language.Haskell.Liquid.Constraint'.
-- The range of the `PVar` substitutions are /fresh/ or /true/ `RefType`. 
-- That is, there are no further `PVar` in the target. 

-------------------------------------------------------------------------------

replacePreds :: String -> SpecType -> [(RPVar, Ref RSort RReft SpecType)] -> SpecType 
replacePreds msg       = foldl' go 
   where go z (π, t@(RPoly _ _)) = substPred msg   (π, t)     z
         go _ (_, RMono _ _)     = error "replacePreds on RMono" -- replacePVarReft (π, r) <$> z


-- TODO: replace `replacePreds` with
-- instance SubsTy RPVar (Ref RReft SpecType) SpecType where
--   subt (pv, r) t = replacePreds "replacePred" t (pv, r)

-- replacePreds :: String -> SpecType -> [(RPVar, Ref Reft RefType)] -> SpecType 
-- replacePreds msg       = foldl' go 
--   where go z (π, RPoly t) = substPred msg   (π, t)     z
--         go z (π, RMono r) = replacePVarReft (π, r) <$> z

-------------------------------------------------------------------------------
substPred :: String -> (RPVar, Ref RSort RReft SpecType) -> SpecType -> SpecType
-------------------------------------------------------------------------------

substPred _   (π, RPoly ss (RVar a1 r1)) t@(RVar a2 r2)
  | isPredInReft && a1 == a2  = RVar a1 $ meetListWithPSubs πs ss r1 r2'
  | isPredInReft              = errorstar ("substPred RVar Var Mismatch" ++ show (a1, a2))
  | otherwise                 = t
  where (r2', πs)             = splitRPvar π r2
        isPredInReft          = not $ null πs 

substPred msg su@(π, _ ) (RApp c ts rs r)
  | null πs                   = t' 
  | otherwise                 = substRCon msg su t' πs r2'
  where t'        = RApp c (substPred msg su <$> ts) (substPredP su <$> rs) r
        (r2', πs) = splitRPvar π r

substPred msg (p, tp) (RAllP (q@(PV _ _ _)) t)
  | p /= q                      = RAllP q $ substPred msg (p, tp) t
  | otherwise                   = RAllP q t 

substPred msg su (RAllT a t)    = RAllT a (substPred msg su t)

substPred msg su@(π,_ ) (RFun x t t' r) 
  | null πs                     = RFun x (substPred msg su t) (substPred msg su t') r
  | otherwise                   = {-meetListWithPSubs πs πt -}(RFun x t t' r')
  where (r', πs)                = splitRPvar π r

substPred msg pt (RCls c ts)    = RCls c (substPred msg pt <$> ts)

substPred msg su (RAllE x t t') = RAllE x (substPred msg su t) (substPred msg su t')
substPred msg su (REx x t t')   = REx   x (substPred msg su t) (substPred msg su t')

substPred _   _  t            = t

-- | Requires: @not $ null πs@
-- substRCon :: String -> (RPVar, SpecType) -> SpecType -> SpecType

substRCon msg (_, RPoly ss (RApp c1 ts1 rs1 r1)) (RApp c2 ts2 rs2 _) πs r2'
  | rTyCon c1 == rTyCon c2    = RApp c1 ts rs $ meetListWithPSubs πs ss r1 r2'
  where ts                    = safeZipWith (msg ++ ": substRCon")  strSub  ts1 ts2
        rs                    = safeZipWith (msg ++ ": substRcon2") strSubR rs1 rs2
        strSub r1 r2          = meetListWithPSubs πs ss r1 r2
        strSubR r1 r2         = meetListWithPSubsRef πs ss r1 r2

substRCon msg su t _ _        = errorstar $ msg ++ " substRCon " ++ showpp (su, t)

substPredP su@(p, RPoly ss tt) (RPoly s t)       
  = RPoly ss' $ substPred "substPredP" su t
 where ss' = if isPredInType p t then (ss ++ s) else s

substPredP _  (RMono _ _)       
  = error $ "RMono found in substPredP"

splitRPvar pv (U x (Pr pvs)) = (U x (Pr pvs'), epvs)
  where (epvs, pvs') = partition (uPVar pv ==) pvs


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
isPredInType p (RCls _ ts) 
  = any (isPredInType p) ts
isPredInType p (RAllE _ t1 t2) 
  = isPredInType p t1 || isPredInType p t2 
isPredInType p (RAppTy t1 t2 r) 
  = isPredInURef p r || isPredInType p t1 || isPredInType p t2
isPredInType _ (RExprArg _)              
  = False
isPredInType _ (ROth _)
  = False

isPredInURef p (U _ (Pr ps)) = any (uPVar p ==) ps


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

meetListWithPSubRef ss (RPoly s1 r1) (RPoly s2 r2) π
  | all (\(_, x, EVar y) -> x == y) (pargs π)
  = RPoly s1 $ r2 `meet` r1      
  | all (\(_, x, EVar y) -> x /= y) (pargs π)
  = RPoly s2 $ r2 `meet` (subst su r1)
  | otherwise
  = errorstar $ "PredType.meetListWithPSubRef partial application to " ++ showpp π
  where su  = mkSubst [(x, y) | (x, (_, _, y)) <- zip (fst <$> s1) (pargs π)]


----------------------------------------------------------------------------
---------- Interface: Modified CoreSyn.exprType due to predApp -------------
----------------------------------------------------------------------------

predName :: String 
predName = "Pred"

predType :: Type 
predType = TyVarTy $ stringTyVar predName

rpredType    :: Reftable r => [RRType r] -> RRType r
rpredType ts = RApp tyc ts [] top
  where 
    tyc      = RTyCon (stringTyCon 'x' 42 predName) [] defaultTyConInfo

defaultTyConInfo = TyConInfo [] [] [] [] Nothing

----------------------------------------------------------------------------
exprType :: CoreExpr -> Type
----------------------------------------------------------------------------

exprType (App e1 (Var v)) | eqType (idType v) predType = exprType e1
exprType (Var var)           = idType var
exprType (Lit lit)           = literalType lit
exprType (Coercion co)       = coercionType co
exprType (Let _ body)        = exprType body
exprType (Case _ _ ty _)     = ty
exprType (Cast _ co)         = pSnd (coercionKind co)
exprType (Tick _ e)          = exprType e
exprType (Lam binder expr)   = mkPiType binder (exprType expr)
exprType e@(App _ _)
  = case collectArgs e of
        (fun, args) -> applyTypeToArgs e (exprType fun) args
exprType _                   = error "PredType : exprType"

-- | Takes a nested application expression and returns the the function
-- being applied and the arguments to which it is applied
collectArgs :: Expr b -> (Expr b, [Arg b])
collectArgs expr
  = go expr []
  where
    go (App f (Var v)) as | eqType (idType v) predType = go f as
    go (App f a) as = go f (a:as)
    go e 	 as = (e, as)


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
substParg (x, y) = fmap fp  -- RJ: UNIFY: BUG  mapTy fxy
  where fxy s = if (s == EVar x) then y else s
        fp    = subvPredicate (\pv -> pv { pargs = mapThd3 fxy <$> pargs pv })

-------------------------------------------------------------------------------
-----------------------------  Predicate Application --------------------------
-------------------------------------------------------------------------------

pappArity  = 2

pappSym n  = S $ "papp" ++ show n

pappSort n = FFunc (2 * n) $ [ptycon] ++ args ++ [bSort]
  where ptycon = fApp (Left predFTyCon) $ FVar <$> [0..n-1]
        args   = FVar <$> [n..(2*n-1)]
        bSort  = FApp boolFTyCon []
 
wiredSortedSyms = [(pappSym n, pappSort n) | n <- [1..pappArity]]

predFTyCon = stringFTycon $ dummyLoc predName

pApp :: Symbol -> [F.Expr] -> Pred
pApp p es= PBexp $ EApp (dummyLoc $ pappSym $ length es) (EVar p:es)

