{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, UndecidableInstances #-}
module Language.Haskell.Liquid.PredType (
    PrType
  , TyConP (..), DataConP (..)
  , splitVsPs, typeAbsVsPs, splitArgsRes
  , generalize, generalizeArgs
  , dataConTy, dataConPtoPredTy, makeTyConInfo
  , removeExtPreds
  , unify, replacePreds, exprType, predType
  , substParg, substPvar
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

import qualified Data.Map  as M
import qualified Data.Set  as S
import Data.List  (partition, foldl')
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Fixpoint hiding (Expr)
import Language.Haskell.Liquid.RefType  hiding (generalize)
import Language.Haskell.Liquid.GhcMisc

import Data.Bifunctor
import Control.Applicative  ((<$>))
import Control.DeepSeq
import Control.Monad.State
import Data.Data

data TyConP = TyConP { freeTyVarsTy :: ![RTyVar]
                     , freePredTy   :: ![(PVar RSort)]
                     }

data DataConP = DataConP { freeTyVars :: ![RTyVar]
                         , freePred   :: ![(PVar RSort)]
                         , tyArgs     :: ![(Symbol, PrType)]
                         , tyRes      :: !PrType
                         }

makeTyConInfo = M.mapWithKey mkRTyCon . M.fromList

mkRTyCon ::  TC.TyCon -> TyConP -> RTyCon
mkRTyCon tc (TyConP αs' ps) = RTyCon tc pvs'
  where τs   = [rVar α :: RSort |  α <- TC.tyConTyVars tc]
        pvs' = subts (zip αs' τs) <$> ps

dataConPtoPredTy :: DataConP -> PrType
dataConPtoPredTy x@(DataConP vs ps yts rt) = {- traceShow ("dataConPtoPredTy: " ++ show x) $ -}  t3						
  where t1 = foldl' (\t2 (x, t1) -> rFun x t1 t2) rt yts 
        t2 = foldr RAllP t1 ps
        t3 = foldr RAllT t2 vs

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

removeExtPreds (RAllP pv t) = removeExtPreds (substPvar (M.singleton pv pdTrue) <$> t) 
removeExtPreds t            = t

dataConTy m (TyVarTy v)            
  = M.findWithDefault (rVar v) (RTV v) m
dataConTy m (FunTy t1 t2)          
  = rFun dummySymbol (dataConTy m t1) (dataConTy m t2)
dataConTy m (ForAllTy α t)          
  = RAllT (rTyVar α) (dataConTy m t)
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
freeArgPreds (RAllT _ t)      = freeArgPreds t
freeArgPreds (RAllP _ t)      = freeArgPreds t
freeArgPreds t                = freePreds t

-- freePreds :: PrType -> S.Set (RPredicate)
freePreds (RVar _ p)       = S.fromList $ pvars p
freePreds (RAllT _ t)      = freePreds t 
freePreds (RAllP p t)      = S.delete p $ freePreds t 
freePreds (RCls _ ts)      = foldl' (\z t -> S.union z (freePreds t)) S.empty ts
freePreds (RFun _ t1 t2 _) = S.union (freePreds t1) (freePreds t2)
freePreds (RApp _ ts ps p) = unions ((S.fromList (concatMap pvars (p:((fromRMono "freePreds") <$> ps)))) : (freePreds <$> ts))

showTyV v = showSDoc $ ppr v <> ppr (varUnique v) <> text "  "
showTy (TyVarTy v) = showSDoc $ ppr v <> ppr (varUnique v) <> text "  "
showTy t = showSDoc $ ppr t

typeAbsVsPs t vs ps = t2
  where t1 = foldr RAllP t  ps  -- RJ: UNIFY reverse?
        t2 = foldr RAllT t1 vs

splitVsPs t = go ([], []) t
  where go (vs, pvs) (RAllT v  t) = go (v:vs, pvs)  t
        go (vs, pvs) (RAllP pv t) = go (vs, pv:pvs) t
        go (vs, pvs) t            = (reverse vs, reverse pvs, t)

splitArgsRes (RFun _ t1 t2 _) = (t1:t1', t2')
  where (t1', t2') = splitArgsRes t2
splitArgsRes t = ([], t)

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
unifyS :: SpecType -> PrType -> State (S.Set RPVar) SpecType 
---------------------------------------------------------------------------

unifyS (RAllP p t) pt
  = do t' <- unifyS t pt 
       s  <- get
       if (p `S.member` s) then return $ RAllP p t' else return t'

unifyS t (RAllP p pt)
  = do t' <- unifyS t pt 
       s  <- get
       if (p `S.member` s) then return $ RAllP p t' else return t'

unifyS (RAllT (v@(RTV α)) t) (RAllT v' pt) 
  = do t'    <- unifyS t $ subsTyVar_meet (v', (rVar α) :: RSort, RVar v pdTrue) pt 
       return $ RAllT v t'

unifyS (RFun x rt1 rt2 _) (RFun x' pt1 pt2 _)
  = do t1' <- unifyS rt1 pt1
       t2' <- unifyS rt2 (substParg (x', x) pt2)
       return $ rFun x t1' t2' 

unifyS t@(RCls c _) (RCls _ _)
  = return t

unifyS (RVar v a) (RVar v' p)
  = do modify $ \s -> s `S.union` (S.fromList $ pvars p) -- (filter (/= PdTrue) [p]))
       return $ RVar v $ bUnify a p

unifyS rt@(RApp c ts rs r) pt@(RApp _ pts ps p)
  = do modify $ \s -> s `S.union` fm
       ts' <- zipWithM unifyS ts pts
       return $ RApp c ts' rs' (bUnify r p)
  where fm       = S.fromList $ concatMap pvars (fp:fps) 
        fp : fps = p : (getR <$> ps)
        rs'      = zipWithZero unifyRef (RMono top {- trueReft -}) pdTrue rs fps
        msg      = "unifyS " ++ showPpr ps -- (rt, pt)
        getR (RMono r) = r
        getR (RPoly _) = top 

unifyS t1 t2                = error ("unifyS" ++ show t1 ++ " with " ++ show t2)

bUnify a (Pr pvs)        = foldl' meet a $ pToReft <$> pvs

unifyRef (RMono a) (Pr pvs) = RMono $ foldl' meet a $ pToReft <$> pvs
unifyRef (RPoly a) (Pr pvs) = RPoly $ foldl' strengthen a $ pToReft <$> pvs

zipWithZero f _  _  []     []     = []
zipWithZero f xz yz []     (y:ys) = (f xz y):(zipWithZero f xz yz [] ys)
zipWithZero f xz yz (x:xs) []     = (f x yz):(zipWithZero f xz yz xs [])
zipWithZero f xz yz (x:xs) (y:ys) = (f x y) :(zipWithZero f xz yz xs ys)
 
-- pToReft p = Reft (vv, [RPvar p]) 
pToReft = U top . pdVar 


----------------------------------------------------------------------------
---------- Interface: Replace Predicate With Type  -------------------------
----------------------------------------------------------------------------

-------------------------------------------------------------------------------
replacePreds :: String -> SpecType -> [(RPVar, Ref Reft SpecType)] -> SpecType 
-------------------------------------------------------------------------------

replacePreds msg = foldl' (flip (replacePred msg)) 

replacePred :: String -> (RPVar, Ref Reft SpecType) -> SpecType -> SpecType
replacePred msg (p, RPoly t) = substPred msg True (p, t)
replacePred msg (p, RMono r) = fmap (replacePVarReft (p, r))


substPred :: String -> Bool -> (RPVar, SpecType) -> SpecType -> SpecType
substPred msg m pv@(p, RVar a1 r1) t@(RVar a2 r2)
  | p `isPredInReft` r2 && a1 == a2
  = if m then RVar a1 ((subst su r1) `meet` r2') else RVar a1 r1
  | p `isPredInReft` r2 
  = error ("substPred RVar var mismatch" ++ show (pv, t))
  | otherwise
  = t
  where (r2', su) = rmRPVarReft p r2

substPred msg m pt@(p, tp) t@(RApp c ts rs r)
  | p `isPredInReft` r
  = if m then substRCon msg pt rcon else tp
  | otherwise 
  = rcon
   where rcon = RApp c (substPred msg m pt <$> ts) (substPredP True pt <$> rs) r

substPred msg m (p, tp) (RAllP (q@(PV _ _ _)) t)
  = RAllP q $ if (p /= q) then (substPred msg m (p, tp) t) else t
substPred msg m pt (RAllT a t) = RAllT a (substPred msg m pt t)
substPred msg m pt@(p, tp) (RFun x t t' r) 
  | p `isPredInReft` r
  = meet (RFun x t t' r') (fmap (subst su) tp)
  | otherwise 
  = RFun x (substPred msg m pt t) (substPred msg m pt t') r
  where (r', su) = rmRPVarReft p r
substPred msg m pt (RCls c ts) = RCls c (substPred msg m pt <$> ts)
substPred msg m pt t = t

substRCon msg (p, RApp c1 ts1 rs1 r1) (RApp c2 ts2 rs2 r2) 
  | rTyCon c1 == rTyCon c2
  =  RApp c1 ts rs $ r2' `meet` (addS r1)
  where (r2', su) = rmRPVarReft p r2
        ts = safeZipWith (msg ++ ": substRCon") (flip strSub) ts1 ts2
        rs = safe0ZipWith (msg ++ ": substRcon2") (flip strSubR) rs1 rs2
        addS r         = subst su r
        strSub t1      = meet t1 . fmap addS
        strSubR t1 t2  = RPoly $ strSub (fromRPoly t1) (fromRPoly t2) 
        

substRCon msg pt t = error $ msg ++ " substRCon " ++ show (pt, t)

-- substPredP :: Bool -> (RPVar, RefType) -> (Ref Reft RefType) -> (Ref Reft RefType)
substPredP b pt (RPoly t) = RPoly $ substPred "substPredP" b pt t
substPredP b pt@(p, _) (RMono r) = error "RMono found in substPredP"


isPredInReft pv (U _ (Pr pvs)) = any (eqPvar pv) pvs 

rmRPVarReft pv (U x (Pr pvs)) = (U x (Pr pvs'), su)
  where (epvs, pvs') = partition (eqPvar pv)  pvs
        su           = case (predArgsSubst . pargs) <$> epvs of
                         [su] -> su
                         _    -> error "Fixpoint.rmRPVarReft"

eqPvar pv1 pv2 = pname pv1 == pname pv2

-- PREDARGS: This substitution makes no sense to me. They are the WRONG args. 
-- Use n2's ...?
replacePVarReft (pv, (Reft (_, ras'))) z@(U (Reft(v, ras)) (Pr pvs)) 
  | length pvs' == length pvs
  = z
  | otherwise
  = U (Reft (v, ras'')) (Pr pvs')
  where pvs'  = filter (not . eqPvar pv)  pvs 
        ras'' = map (subst (predArgsSubst (pargs pv))) ras'
  
predArgsSubst = mkSubst . map (\(_, s1, s2) -> (s1, EVar s2)) 

----------------------------------------------------------------------------
---------- Interface: Modified CoreSyn.exprType due to predApp -------------
----------------------------------------------------------------------------

predType :: Type 
predType = TyVarTy $ stringTyVar "Pred"

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

substPvar :: M.Map RPVar RPredicate -> RPredicate -> RPredicate 
substPvar s = (\(Pr πs) -> pdAnd (lookupP s <$> πs))

substParg :: Functor f =>(Symbol, Symbol) -> f (Predicate ty) -> f (Predicate ty)
substParg (x, y) = fmap fp  -- RJ: UNIFY: BUG  mapTy fxy
  where fxy s = if (s == x) then y else s
        fp    = subvPredicate (\pv -> pv { pargs = mapThd3 fxy <$> pargs pv })

lookupP ::  M.Map (PVar t) (Predicate t) -> PVar t -> Predicate t
lookupP s p@(PV _ _ s')
  = case M.lookup p s of 
      Nothing  -> Pr [p]
      Just q   -> subvPredicate (\pv -> pv { pargs = s'}) q

------------------------------------------------------------------------------
-- RIPPING PredVar Stuff out of Fixpoint
------------------------------------------------------------------------------

{-
  -- Related to PVar
  , isPredInReft, rmRPVar, rmRPVarReft
  , replacePVarReft
 
--replaceRPvarRefa (PV n1 _ args) (Reft (_, ras)) (PV n2 _ _)
--  | n1 == n2
--  = map (subst (predArgsSubst args)) ras
--  | otherwise
--  = ras
--replaceRPvarRefa _ r = [r]
-
-- rmRPVar s r = fst $ rmRPVarReft s r

-- isPredInReft p (Reft(_, ls)) = or (isPredInRefa p <$> ls)
-- isPredInRefa p (RPvar p')    = isSamePvar p p'
-- isPredInRefa _ _             = False
-- isSamePvar (PV s1 _ _) (PV s2 _ _) = s1 == s2
--
-- rmRPVarReft s (Reft(v, ls)) = (Reft(v, ls'), su)
--   where (l, s1) = unzip $ map (rmRPVarRefa s) ls
--         ls' = catMaybes l
--         su = case catMaybes s1 of {[su'] -> su'; _ -> error "Fixpoint.rmRPVarReft"}
--
-- rmRPVarRefa (PV s1 _ _) r@(RPvar (PV s2 _ a2))
--   | s1 == s2
--   = (Nothing, Just $ predArgsSubst a2)
--   | otherwise
--   = (Just r, Nothing) 
-- 
-- rmRPVarRefa _ r
--   = (Just r, Nothing)



-}
