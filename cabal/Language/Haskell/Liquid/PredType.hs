{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, UndecidableInstances #-}
module Language.Haskell.Liquid.PredType (
    PrType
  , TyConP (..), DataConP (..)
  , dataConTy, dataConPtoPredTy, makeTyConInfo
  , unify, replacePreds, exprType, predType
  , substParg
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
import Data.List        (nub, partition, foldl')
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

showTyV v = showSDoc $ ppr v <> ppr (varUnique v) <> text "  "
showTy (TyVarTy v) = showSDoc $ ppr v <> ppr (varUnique v) <> text "  "
showTy t = showSDoc $ ppr t

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
unifyS :: SpecType -> PrType -> State (S.Set UsedPVar) SpecType 
---------------------------------------------------------------------------

unifyS (RAllP p t) pt
  = do t' <- unifyS t pt 
       s  <- get
       if (uPVar p `S.member` s) then return $ RAllP p t' else return t'

unifyS t (RAllP p pt)
  = do t' <- unifyS t pt 
       s  <- get
       if (uPVar p `S.member` s) then return $ RAllP p t' else return t'

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

-- | This is the main function used to substitute an (abstract) predicate
-- with a concrete Ref, either a base (`RMono`) refinement or a compound
-- (`RPoly`) type. The substitution is invoked to obtain the `SpecType` 
-- resulting at /predicate application/ sites in 'Language.Haskell.Liquid.Constraint'.
-- The range of the `PVar` substitutions are /fresh/ or /true/ `RefType`. 
-- That is, there are no further `PVar` in the target. 

-------------------------------------------------------------------------------

replacePreds :: String -> SpecType -> [(RPVar, Ref RReft SpecType)] -> SpecType 
replacePreds msg       = foldl' go 
   where go z (π, RPoly t) = substPred msg   (π, t)     z
         go z (π, RMono r) = replacePVarReft (π, r) <$> z


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

substPred msg (π, RVar a1 r1) t@(RVar a2 r2)
  | π `isPredInReft` r2 && a1 == a2 = RVar a1 ((subst su r1) `meet` r2') 
  | π `isPredInReft` r2             = errorstar ("substPred RVar Var Mismatch")
  | otherwise                       = t
  where (r2', su) = rmRPVarReft π r2

substPred msg su@(π, πt) t@(RApp c ts rs r)
  | π `isPredInReft` r              = substRCon msg su t' 
  | otherwise                       = t' 
  where t' = RApp c (substPred msg su <$> ts) (substPredP su <$> rs) r

substPred msg (p, tp) (RAllP (q@(PV _ _ _)) t)
  | p /= q                          = RAllP q $ substPred msg (p, tp) t
  | otherwise                       = RAllP q t 

substPred msg su (RAllT a t)        = RAllT a (substPred msg su t)

substPred msg su@(π, πt) (RFun x t t' r) 
  | π `isPredInReft` r              = (RFun x t t' r') `meet` (subst su' πt)
  | otherwise                       = RFun x (substPred msg su t) (substPred msg su t') r
  where (r', su')                   = rmRPVarReft π r

substPred msg pt (RCls c ts)        = RCls c (substPred msg pt <$> ts)

substPred msg pt t                  = t

-- | Requires: @p `isPredInReft` r@
substRCon :: String -> (RPVar, SpecType) -> SpecType -> SpecType
substRCon msg (π, RApp c1 ts1 rs1 r1) (RApp c2 ts2 rs2 r2) 
  | rTyCon c1 == rTyCon c2          = RApp c1 ts rs $ r2' `meet` subst su r1
  where (r2', su)                   = rmRPVarReft π r2
        ts                          = safeZipWith (msg ++ ": substRCon")   strSub  ts1 ts2
        rs                          = safe0ZipWith (msg ++ ": substRcon2") strSubR rs1 rs2
        strSub t1 t2                = t2 `meet` subst su t1
        strSubR r1 r2               = RPoly $ strSub (fromRPoly r1) (fromRPoly r2)                             

substRCon msg su t                  = errorstar $ msg ++ " substRCon " ++ show (su, t)

substPredP su (RPoly t)             = RPoly $ substPred "substPredP" su t
substPredP _  (RMono r)             = error $ "RMono found in substPredP"


-- | The next two functions should be combined into a single one that
-- checks and extracts the relevant predicate substitution. They are used
-- more or less "atomically" in the `substPred` above.

isPredInReft pv (U _ (Pr pvs)) = any (uPVar pv ==) pvs 

-- | Requires @pv `isPredInReft` r@
-- Actually, it is ok to have /multiple/ `su` you just have to replace
-- with /multiple copies/ of the corresponding Refa
rmRPVarReft pv r@(U x (Pr pvs)) = (U x (Pr pvs'), su)
  where (epvs, pvs') = partition (uPVar pv ==)  pvs
        su           = case nub ((predArgsSubst . pargs) <$> epvs) of
                         [su] -> su
                         zs   -> errorstar $ "Fixpoint.rmRPVarReft: " ++ show zs ++ " ."

-- PREDARGS: This substitution makes no sense. They are the WRONG args. Use n2's ...?
replacePVarReft (pv, (U (Reft (_, ras')) p')) z@(U (Reft(v, ras)) (Pr pvs)) 
  | length pvs' == length pvs
  = z
  | otherwise
  = U (Reft (v, ras'')) (pdAnd [p', Pr pvs'])
  where pvs'  = filter (uPVar pv /=)  pvs 
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

substParg :: Functor f => (Symbol, Symbol) -> f Predicate -> f Predicate
substParg (x, y) = fmap fp  -- RJ: UNIFY: BUG  mapTy fxy
  where fxy s = if (s == x) then y else s
        fp    = subvPredicate (\pv -> pv { pargs = mapThd3 fxy <$> pargs pv })

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
