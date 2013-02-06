{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, UndecidableInstances, TupleSections #-}
module Language.Haskell.Liquid.PredType (
    PrType
  , TyConP (..), DataConP (..)
  , dataConTy, dataConPSpecType, makeTyConInfo
  , unify, replacePreds, exprType, predType
  , replacePredsWithRefs, pVartoRConc, toPredType
  , substParg
  ) where

import PprCore          (pprCoreExpr)
import Id               (idType)
import CoreSyn  hiding (collectArgs)
import Type
import TypeRep
import qualified TyCon as TC
import Literal
import Coercion         (coercionType, coercionKind)
import Pair             (pSnd)
import FastString       (sLit)
import Outputable hiding (empty)

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import Data.List        (partition, foldl')
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Fixpoint hiding (Expr)
import qualified Language.Haskell.Liquid.Fixpoint as F
import Language.Haskell.Liquid.RefType  hiding (generalize)
import Language.Haskell.Liquid.GhcMisc

import Control.Applicative  ((<$>))
import Control.Monad.State

data TyConP = TyConP { freeTyVarsTy :: ![RTyVar]
                     , freePredTy   :: ![(PVar RSort)]
                     }

data DataConP = DataConP { freeTyVars :: ![RTyVar]
                         , freePred   :: ![(PVar RSort)]
                         , tyArgs     :: ![(Symbol, SpecType)]
                         , tyRes      :: !SpecType
                         }

makeTyConInfo = hashMapMapWithKey mkRTyCon . M.fromList

mkRTyCon ::  TC.TyCon -> TyConP -> RTyCon
mkRTyCon tc (TyConP αs' ps) = RTyCon tc pvs' (getTyConInfo tc)
  where τs   = [rVar α :: RSort |  α <- TC.tyConTyVars tc]
        pvs' = subts (zip αs' τs) <$> ps

dataConPSpecType :: DataConP -> SpecType 
dataConPSpecType (DataConP vs ps yts rt) = mkArrow vs ps (reverse yts) rt 
--   where t1 = foldl' (\t2 (x, t1) -> rFun x t1 t2) rt yts 
--         t2 = foldr RAllP t1 ps
--         t3 = foldr RAllT t2 vs


instance Outputable TyConP where
  ppr (TyConP vs ps) = (parens $ hsep (punctuate comma (map ppr vs))) <+>
                       (parens $ hsep (punctuate comma (map ppr ps)))

instance Show TyConP where
 show = showSDoc . ppr

instance Outputable DataConP where
 ppr (DataConP vs ps yts t) 
   = (parens $ hsep (punctuate comma (map ppr vs))) <+>
     (parens $ hsep (punctuate comma (map ppr ps))) <+>
     (parens $ hsep (punctuate comma (map ppr yts))) <+>
     ppr t

instance Show DataConP where
 show = showSDoc . ppr

dataConTy m (TyVarTy v)            
  = M.lookupDefault (rVar v) (RTV v) m
dataConTy m (FunTy t1 t2)          
  = rFun dummySymbol (dataConTy m t1) (dataConTy m t2)
dataConTy m (ForAllTy α t)          
  = RAllT (rTyVar α) (dataConTy m t)
dataConTy _ t
  | isPredTy t
  = ofPredTree $ classifyPredType t
dataConTy m (TyConApp c ts)        
  = rApp c (dataConTy m <$> ts) [] pdTrue
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
  = do t'    <- unifyS t $ subsTyVar_meet (v', (rVar α) :: RSort, RVar v pdTrue) pt 
       return $ RAllT v t'

unifyS (RFun x rt1 rt2 _) (RFun x' pt1 pt2 _)
  = do t1' <- unifyS rt1 pt1
       t2' <- unifyS rt2 (substParg (x', EVar x) pt2)
       return $ rFun x t1' t2' 

unifyS (RAppTy rt1 rt2 _) (RAppTy pt1 pt2 _)
  = do t1' <- unifyS rt1 pt1
       t2' <- unifyS rt2 pt2
       return $ rAppTy t1' t2'

unifyS t@(RCls _ _) (RCls _ _)
  = return t

unifyS (RVar v a) (RVar _ p)
  = do modify $ \s -> s `S.union` (S.fromList $ pvars p) -- (filter (/= PdTrue) [p]))
       return $ RVar v $ bUnify a p

unifyS (RApp c ts rs r) (RApp _ pts ps p)
  = do modify $ \s -> s `S.union` fm
       ts' <- zipWithM unifyS ts pts
       return $ RApp c ts' rs' (bUnify r p)
  where fm       = S.fromList $ concatMap pvars (fp:fps) 
        fp : fps = p : (getR <$> ps)
        rs'      = zipWithZero unifyRef (RMono top {- trueReft -}) pdTrue rs fps
        getR (RMono r) = r
        getR (RPoly _) = top 

unifyS (REx x tx t) (REx x' _ t') | x == x'
  = liftM (REx x tx) (unifyS t t')

unifyS t1 t2                
  = error ("unifyS" ++ show t1 ++ " with " ++ show t2)

bUnify a (Pr pvs)        = foldl' meet a $ pToReft <$> pvs

unifyRef (RMono a) (Pr pvs) = RMono $ foldl' meet a $ pToReft <$> pvs
unifyRef (RPoly a) (Pr pvs) = RPoly $ foldl' strengthen a $ pToReft <$> pvs

zipWithZero _ _  _  []     []     = []
zipWithZero f xz yz []     (y:ys) = (f xz y):(zipWithZero f xz yz [] ys)
zipWithZero f xz yz (x:xs) []     = (f x yz):(zipWithZero f xz yz xs [])
zipWithZero f xz yz (x:xs) (y:ys) = (f x y) :(zipWithZero f xz yz xs ys)
 
-- pToReft p = Reft (vv, [RPvar p]) 
pToReft = U top . pdVar 

----------------------------------------------------------------------------
----- Interface: Replace Predicate With Uninterprented Function Symbol -----
----------------------------------------------------------------------------

replacePredsWithRefs (p, r) (U fr (Pr ps)) 
  = U (FSReft (freeSymbols++s) (Reft (v, rs ++ rs'))) (Pr ps2)
  where rs'              = r . (v,) . pargs <$> ps1
        (ps1, ps2)       = partition (==p) ps
        (s, Reft(v, rs)) = splitFReft fr
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

replacePreds :: String -> SpecType -> [(RPVar, Ref RReft SpecType)] -> SpecType 
replacePreds msg       = foldl' go 
   where go z (π, RPoly t) = substPred msg   (π, t)     z
         go _ (_, RMono _) = error "replacePreds on RMono" -- replacePVarReft (π, r) <$> z


-- TODO: replace `replacePreds` with
-- instance SubsTy RPVar (Ref RReft SpecType) SpecType where
--   subt (pv, r) t = replacePreds "replacePred" t (pv, r)

-- replacePreds :: String -> SpecType -> [(RPVar, Ref Reft RefType)] -> SpecType 
-- replacePreds msg       = foldl' go 
--   where go z (π, RPoly t) = substPred msg   (π, t)     z
--         go z (π, RMono r) = replacePVarReft (π, r) <$> z

-------------------------------------------------------------------------------
substPred :: String -> (RPVar, SpecType) -> SpecType -> SpecType
-------------------------------------------------------------------------------

substPred _   (π, RVar a1 r1) t@(RVar a2 r2)
  | isPredInReft && a1 == a2  = RVar a1 $ meetListWithPSubs πs r1 r2'
  | isPredInReft              = errorstar ("substPred RVar Var Mismatch")
  | otherwise                 = t
  where (r2', πs)             = splitRPvar π r2
        isPredInReft          = not $ null πs 

substPred msg su@(π, _ ) (RApp c ts rs r)
  | null πs                   = t' 
  | otherwise                 = substRCon msg su t' πs r2'
  where t'        = RApp c (substPred msg su <$> ts) (substPredP su <$> rs) r
        (r2', πs) = splitRPvar π r

substPred msg (p, tp) (RAllP (q@(PV _ _ _)) t)
  | p /= q                    = RAllP q $ substPred msg (p, tp) t
  | otherwise                 = RAllP q t 

substPred msg su (RAllT a t)  = RAllT a (substPred msg su t)

substPred msg su@(π, πt) (RFun x t t' r) 
  | null πs                   = RFun x (substPred msg su t) (substPred msg su t') r
  | otherwise                 = meetListWithPSubs πs πt (RFun x t t' r')
  where (r', πs)              = splitRPvar π r

substPred msg pt (RCls c ts)  = RCls c (substPred msg pt <$> ts)

substPred msg su (REx x t t') = REx x (substPred msg su t) (substPred msg su t')

substPred _   _  t            = t

-- | Requires: @not $ null πs@
-- substRCon :: String -> (RPVar, SpecType) -> SpecType -> SpecType

substRCon msg (_, RApp c1 ts1 rs1 r1) (RApp c2 ts2 rs2 _) πs r2'
  | rTyCon c1 == rTyCon c2    = RApp c1 ts rs $ meetListWithPSubs πs r1 r2'
  where ts                    = safeZipWith (msg ++ ": substRCon")  strSub  ts1 ts2
        rs                    = safeZipWith (msg ++ ": substRcon2") strSubR rs1 rs2
        strSub r1 r2          = meetListWithPSubs πs (addSyms ss r1)r2
        strSubR r1 r2         = RPoly $ strSub (fromRPoly r1) (fromRPoly r2)                             
        ss = fSyms (RApp c1 ts1 rs1 r1)

substRCon msg su t _ _        = errorstar $ msg ++ " substRCon " ++ show (su, t)

substPredP su (RPoly t)       = RPoly $ substPred "substPredP" su t
substPredP _  (RMono _)       = error $ "RMono found in substPredP"

splitRPvar pv (U x (Pr pvs)) = (U x (Pr pvs'), epvs)
  where (epvs, pvs') = partition (uPVar pv ==) pvs

meetListWithPSubs πs r1 r2 = foldl' (meetListWithPSub r1) r2 πs

meetListWithPSub ::  Reftable r => r -> r -> PVar t -> r
meetListWithPSub r1 r2 π
  | all (\(_, x, EVar y) -> x == y) (pargs π)
  = addSyms (fSyms r1) $ r2 `meet` r1'      
  | all (\(_, x, EVar y) -> x /= y) (pargs π)
  = r2 `meet` (subst su r1')
  | otherwise
  = errorstar $ "PredType.meetListWithPSub partial application to " ++ showPpr π
  where r1' = dropSyms r1
        su  = mkSubst xys
        xys = [(x, y) | (x, (_, _, y)) <- zip (fSyms r1) (pargs π)]

----------------------------------------------------------------------------
---------- Interface: Modified CoreSyn.exprType due to predApp -------------
----------------------------------------------------------------------------

predType :: Type 
predType = TyVarTy $ stringTyVar "Pred"

rpredType :: Reftable r => [RRType r] -> RRType r
rpredType ts
  = RApp tyc ts [] top
  where tyc = RTyCon (stringTyCon 'x' 42 "Pred") [] defaultTyConInfo

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

applyTypeToArgs :: CoreExpr -> Type -> [CoreExpr] -> Type
-- ^ A more efficient version of 'applyTypeToArg' when we have several arguments.
-- The first argument is just for debugging, and gives some context
applyTypeToArgs _ op_ty [] = op_ty

applyTypeToArgs e op_ty (Type ty : args)
  =     -- Accumulate type arguments so we can instantiate all at once
    go [ty] args
  where
    go rev_tys (Type ty : args) = go (ty:rev_tys) args
    go rev_tys rest_args         = applyTypeToArgs e op_ty' rest_args
                                 where
                                   op_ty' = applyTysD msg op_ty (reverse rev_tys)
                                   msg = ptext (sLit "MYapplyTypeToArgs") <+>
                                         panic_msg e op_ty

applyTypeToArgs e op_ty (_ : args)
  = case (splitFunTy_maybe op_ty) of
        Just (_, res_ty) -> applyTypeToArgs e res_ty args
        Nothing          -> pprPanic "MYapplyTypeToArgs" (panic_msg e op_ty)

panic_msg :: CoreExpr -> Type -> SDoc
panic_msg e op_ty = pprCoreExpr e $$ ppr op_ty

substParg :: Functor f => (Symbol, F.Expr) -> f Predicate -> f Predicate
substParg (x, y) = fmap fp  -- RJ: UNIFY: BUG  mapTy fxy
  where fxy s = if (s == EVar x) then y else s
        fp    = subvPredicate (\pv -> pv { pargs = mapThd3 fxy <$> pargs pv })

