{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, UndecidableInstances #-}
module Language.Haskell.Liquid.PredType (
    PrType
  , TyConP (..), DataConP (..)
  , splitVsPs, typeAbsVsPs, splitArgsRes
  , generalize, generalizeArgs
  , dataConTy, dataConPtoPredTy
  , removeExtPreds
  , unify, replacePred, exprType, predType
  , substParg, substPvar, mapPvar
  ) where

import PprCore          (pprCoreExpr)
import Id               (idType)
import Class
import CoreSyn  hiding (collectArgs)
import Type
import TcType
import TypeRep
import qualified TyCon as TC
import Literal
import Class
import Var 
import Unique           (getUnique)
import Coercion         (coercionType, coercionKind)
import Pair             (pSnd)
import FastString       (sLit)
import Outputable hiding (empty)

import qualified Data.List as L
import qualified Data.Map  as M
import qualified Data.Set  as S
import Data.List  (foldl')
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Fixpoint hiding (Expr)
import Language.Haskell.Liquid.RefType  hiding (generalize)
import Language.Haskell.Liquid.GhcMisc

import Data.Bifunctor
import Control.Applicative  ((<$>))
import Control.DeepSeq
import Control.Monad.State
import Data.Data

predType :: Type
predType = TyVarTy $ stringTyVar "Pred"

data TyConP = TyConP { freeTyVarsTy :: ![RTyVar]
                     , freePredTy   :: ![(PVar Type)]
                     }

data DataConP = DataConP { freeTyVars :: ![RTyVar]
                         , freePred   :: ![(PVar Type)]
                         , tyArgs     :: ![(Symbol, PrType)]
                         , tyRes      :: !PrType
                         }

dataConPtoPredTy :: DataConP -> PrType
dataConPtoPredTy x@(DataConP vs ps yts rt) = {- traceShow ("dataConPtoPredTy: " ++ show x) $ -}  t3						
  where t1 = foldl' (\t2 (x, t1) -> rFun (RB x) t1 t2) rt yts 
        t2 = foldr RAll t1 $ RP <$> ps
        t3 = foldr RAll t2 $ RV <$> vs

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

removeExtPreds (RAll (RP pv)  t) = removeExtPreds (substPvar (M.singleton pv pdTrue) <$> t) 
-- removeExtPreds t@(RAll (RV _) _) = t
removeExtPreds t                 = t

dataConTy m (TyVarTy v)            
  = M.findWithDefault (rVar v pdTrue) (RTV v) m
dataConTy m (FunTy t1 t2)          
  = rFun (RB dummySymbol) (dataConTy m t1) (dataConTy m t2)
dataConTy m (ForAllTy α t)          
  = RAll (rTyVar α) (dataConTy m t)
dataConTy m t
  | isPredTy t
  = ofPredTree $ classifyPredType t
dataConTy m (TyConApp c ts)        
  = rApp c (dataConTy m <$> ts) [] pdTrue
dataConTy _ t
  = error "ofTypePAppTy"

generalize     = generalize_ freePreds
generalizeArgs = generalize_ freeArgPreds

generalize_ f t = typeAbsVsPs t' vs ps
  where (vs, ps', t') = splitVsPs t
        ps            = (S.toList (f t)) ++ ps'

freeArgPreds (RFun _ t1 t2 _) = freePreds t1 -- RJ: UNIFY What about t2?
freeArgPreds (RAll _ t)       = freeArgPreds t
freeArgPreds t                = freePreds t

-- freePreds :: PrType -> S.Set (Predicate Type)
freePreds (RVar _ p)       = S.fromList $ pvars p
freePreds (RAll (RV _) t)  = freePreds t 
freePreds (RAll (RP p) t)  = S.delete p $ freePreds t 
freePreds (RCls _ ts)      = foldl' (\z t -> S.union z (freePreds t)) S.empty ts
freePreds (RFun _ t1 t2 _) = S.union (freePreds t1) (freePreds t2)
freePreds (RApp _ ts ps p) = unions ((S.fromList (concatMap pvars (p:((fromRMono "freePreds") <$> ps)))) : (freePreds <$> ts))

showTyV v = showSDoc $ ppr v <> ppr (varUnique v) <> text "  "
showTy (TyVarTy v) = showSDoc $ ppr v <> ppr (varUnique v) <> text "  "
showTy t = showSDoc $ ppr t

typeAbsVsPs t vs ps = t2
  where t1 = foldr RAll t  (RP <$> ps)  -- RJ: UNIFY reverse?
        t2 = foldr RAll t1 (RV <$> vs)

splitVsPs t = go ([], []) t
  where go (vs, pvs) (RAll (RV v)  t) = go (v:vs, pvs)  t
        go (vs, pvs) (RAll (RP pv) t) = go (vs, pv:pvs) t
        go (vs, pvs) t                = (reverse vs, reverse pvs, t)

splitArgsRes (RFun _ t1 t2 _) = (t1:t1', t2')
  where (t1', t2') = splitArgsRes t2
splitArgsRes t = ([], t)

---------------------------------------------------------------------------
-------------- Interfacing Between Predicates and Refinements -------------
---------------------------------------------------------------------------

---------------------------------------------------------------------------
--------------Interfacing: Unify PrType with RefType ----------------------
---------------------------------------------------------------------------

---------------------------------------------------------------------------
unify :: Maybe PrType -> RefType -> RefType 
---------------------------------------------------------------------------

unify (Just pt) rt  = evalState (unifyS rt pt) S.empty
unify _         t   = t

unifyS :: RefType -> PrType -> State (S.Set (PVar Type)) RefType

unifyS (RAll (RP p) t) pt
  = do t' <- unifyS t pt 
       s  <- get
       if (p `S.member` s) then return $ RAll (RP p) t' else return t'

unifyS t (RAll (RP p) pt)
  = do t' <- unifyS t pt 
       s  <- get
       if (p `S.member` s) then return $ RAll (RP p) t' else return t'

unifyS (RAll (RV v@(RTV α)) t) (RAll (RV v') pt) 
  = do t' <-  unifyS t $ subsTyVar_meet (v', TyVarTy α, RVar (RV v) pdTrue) pt 
       return $ RAll (RV v) t'

unifyS (RFun (RB x) rt1 rt2 _) (RFun (RB x') pt1 pt2 _)
  = do t1' <- unifyS rt1 pt1
       t2' <- unifyS rt2 (substParg (x', x) pt2)
       return $ rFun (RB x) t1' t2' 

unifyS t@(RCls c _) (RCls _ _)
  = return t

unifyS (RVar (RV v) a) (RVar (RV v') p)
  = do modify $ \s -> s `S.union` (S.fromList $ pvars p) -- (filter (/= PdTrue) [p]))
       return $ RVar (RV v) $ bUnify a p

unifyS rt@(RApp c ts rs r) pt@(RApp _ pts ps p)
  = do modify $ \s -> s `S.union` fm
       ts' <- zipWithM unifyS ts pts
       return $ RApp c ts' rs' (bUnify r p)
  where fm       = S.fromList $ concatMap pvars (fp:fps) 
        fp : fps = p : (getR <$> ps)
        rs'      = zipWithZero unifyRef (RMono trueReft) pdTrue rs fps
        msg      = "unifyS " ++ showPpr ps -- (rt, pt)
        getR (RMono r) = r
        getR (RPoly _) = top 

unifyS t1 t2                = error ("unifyS" ++ show t1 ++ " with " ++ show t2)
bUnify a (Pr pvs)           = foldl' meet a $ pToReft <$> pvs

unifyRef (RMono a) (Pr pvs) = RMono $ foldl' meet a $ pToReft <$> pvs
unifyRef (RPoly a) (Pr pvs) = RPoly $ foldl' strengthen a $ pToReft <$> pvs

zipWithZero f _  _  []     []     = []
zipWithZero f xz yz []     (y:ys) = (f xz y):(zipWithZero f xz yz [] ys)
zipWithZero f xz yz (x:xs) []     = (f x yz):(zipWithZero f xz yz xs [])
zipWithZero f xz yz (x:xs) (y:ys) = (f x y) :(zipWithZero f xz yz xs ys)
 
pToReft p = Reft (vv, [RPvar p]) 

----------------------------------------------------------------------------
---------- Interface: Replace Predicate With Type  -------------------------
----------------------------------------------------------------------------

----------------------------------------------------------------------------
replacePred :: (PVar Type, Ref Reft RefType) -> RefType -> RefType
----------------------------------------------------------------------------

replacePred pr@(p, RPoly t)  t0 = substPred True (p, t) t0
replacePred pr@(p, RMono r)  t0 = fmap (replacePVarReft (p, r)) t0

substPredP :: Bool -> (PVar Type, RefType) -> (Ref Reft RefType) -> (Ref Reft RefType)
substPredP b pt (RPoly t) = RPoly $ substPred b pt t
substPredP b pt@(p, _) (RMono r) = error "RMono found in substPredP"
{-  | p `isPredIn` r
  = RPoly $ substPred b pt ((ofType (ptype p)) `strengthen` r)
  | otherwise 
  = RMono r
-}

substPred m pv@(p, RVar a1 r1) t@(RVar a2 r2)
  | ispInr2 && a1 == a2
  = if m then RVar a1 ((subst su r1) `mymeet` r2') else RVar a1 r1
  | otherwise
  = if ispInr2 
     then error ("substPred RVar var mismatch" ++ show (pv, t))
          else t
  where (r2', su) = rmKVarReft p r2
        ispInr2   = p `isPredIn` r2

substPred m pt@(p, tp) t@(RApp c ts rs r)
  | p `isPredIn` r
  = if m then substRCon pt rcon else tp
  | otherwise 
  = rcon
   where rcon = RApp c (substPred m pt <$> ts) (substPredP True pt <$> rs) r

substPred m (p, tp) (RAll (RP q@(PV _ _ _)) t)
  = RAll (RP q) $ if (p/=q) then (substPred m (p, tp) t) else t
substPred m pt (RAll a@(RV _) t) = RAll a (substPred m pt t)
substPred m pt@(p, tp) (RFun x t t' r) 
  | p `isPredIn` r
  = {- strengthenRefType -} meet (RFun x t t' r') (fmap (subst su) tp)
  | otherwise 
  = RFun x (substPred m pt t) (substPred m pt t') r
  where (r', su) = rmKVarReft p r
substPred m pt (RCls c ts) = RCls c (substPred m pt <$> ts)
substPred m pt t = t

substRCon (p, RApp c1 ts1 rs1 r1) (RApp c2 ts2 rs2 r2) | rc1 == rc2
  =  RApp c1 ts rs $ r2' `mymeet` (addS r1)
  where (r2', su) = rmKVarReft p r2
        ts = safeZipWith "substRCon" (flip strSub) ts1 ts2
        rs = safeZipWith "substRcon2" (flip strSubR) rs1 rs2
        addS r         = subst su r
        (RTyCon rc1 _) = c1
        (RTyCon rc2 _) = c2
        strSub t1      = {- strengthenRefType -} meet t1 . fmap addS
        strSubR t1 t2  = RPoly $ strSub (fromRPoly t1) (fromRPoly t2) 

substRCon pt t = error $ "substRCon" ++ show (pt, t)

mymeet x y = meet x y
isPredIn = isPredInReft

rmKVarReft = rmRPVarReft

----------------------------------------------------------------------------
---------- Interface: Modified CoreSyn.exprType due to predApp -------------
----------------------------------------------------------------------------

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


applyTypeToArgs e op_ty (p : args)
  = case (splitFunTy_maybe op_ty) of
        Just (_, res_ty) -> applyTypeToArgs e res_ty args
        Nothing -> pprPanic "MYapplyTypeToArgs" (panic_msg e op_ty)

panic_msg :: CoreExpr -> Type -> SDoc
panic_msg e op_ty = pprCoreExpr e $$ ppr op_ty

substPvar :: M.Map (PVar Type) (Predicate Type) -> Predicate Type -> Predicate Type 
substPvar s = (\(Pr πs) -> pdAnd (lookupP s <$> πs))

substParg (x, y) = fmap fp  -- RJ: UNIFY: BUG  mapTy fxy
  where fxy s = if (s == x) then y else s
        fp    = mapPvar (\pv -> pv { pargs = mapThd3 fxy <$> pargs pv })

mapPvar :: (PVar ty -> PVar ty) -> Predicate ty -> Predicate ty 
mapPvar f (Pr pvs) = Pr (f <$> pvs)

lookupP s p@(PV _ _ s')
  = case M.lookup p s of 
      Nothing  -> Pr [p]
      Just q   -> mapPvar (\pv -> pv { pargs = s'}) q

-- subv_prtype :: (PVar Type -> PVar Type) -> PrType -> PrType
-- subv_prtype = fmap . subv_predicate 
--subv_type :: (PVar Type -> PVar Type) -> Type -> Type
--subv_type _ = id  
-- subp :: M.Map (PVar Type) (Predicate Type) -> PrType -> PrType 
-- subp = error "TODO: subp"
-- subp s (Pr pvs) = pdAnd (lookupP s <$> pvs) -- RJ: UNIFY: not correct!
