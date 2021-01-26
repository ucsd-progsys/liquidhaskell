{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeSynonymInstances       #-}

-- | This module defines the representation of Subtyping and WF Constraints,
--   and the code for syntax-directed constraint generation.

module Language.Haskell.Liquid.Constraint.Relational (consRelTop) where

#if !MIN_VERSION_base(4,14,0)
import           Control.Monad.Fail
#endif

import           Control.Monad.State
import qualified Data.HashMap.Strict                            as M
import qualified Data.List                                      as L
import           Data.String                                    ( IsString(..) )
import qualified Debug.Trace                                    as D
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types                        as F
import qualified Language.Fixpoint.Types.Names                  as F
import qualified Language.Fixpoint.Types.Visitor                as F
import           Language.Haskell.Liquid.Bare.DataType          (makeDataConChecker)
import           Language.Haskell.Liquid.Constraint.Constraint
import           Language.Haskell.Liquid.Constraint.Env
import           Language.Haskell.Liquid.Constraint.Fresh
import           Language.Haskell.Liquid.Constraint.Init
import           Language.Haskell.Liquid.Constraint.Monad
import           Language.Haskell.Liquid.Constraint.Split
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.GHC.API                as Ghc hiding
                                                                       (checkErr,
                                                                        panic,
                                                                        text,
                                                                        trace,
                                                                        vcat,
                                                                        (<+>))
import qualified Language.Haskell.Liquid.GHC.Misc               as GM
import           Language.Haskell.Liquid.GHC.Play               (isHoleVar, Subable(sub))
import qualified Language.Haskell.Liquid.GHC.Resugar            as Rs
import qualified Language.Haskell.Liquid.GHC.SpanStack          as Sp
import           Language.Haskell.Liquid.GHC.TypeRep            ()
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.Transforms.CoreToLogic (weakenResult)
import           Language.Haskell.Liquid.Transforms.Rec
import           Language.Haskell.Liquid.Types.Dictionaries
import           Text.PrettyPrint.HughesPJ                      hiding ((<>))

import           Language.Haskell.Liquid.Types                  hiding (Def,
                                                                 Loc, binds,
                                                                 loc)

consRelTop :: Config -> TargetInfo -> CGEnv -> (Var, Var, LocSpecType, LocSpecType, F.Expr) -> CG ()
consRelTop _ ti γ (x,y,t,s,p) = do
  let cbs = giCbs $ giSrc ti
  let e = findBody x cbs
  let d = findBody y cbs
  let e' = traceChk "Init" e d t s p e
  consRelCheck (γ `setLocation` Sp.Span (GM.fSrcSpan (F.loc t))) [] e' d (val t) (val s) p

--------------------------------------------------------------
-- Core Checking Rules ---------------------------------------
--------------------------------------------------------------

type PrEnv = [F.Expr]
type RelAlt = (AltCon, [Var], [Var], CoreExpr, CoreExpr)

resL, resR :: F.Symbol
resL = fromString "r1"
resR = fromString "r2"

-- Definition of CoreExpr: https://hackage.haskell.org/package/ghc-8.10.1/docs/CoreSyn.html
consRelCheck :: CGEnv -> PrEnv -> CoreExpr -> CoreExpr -> 
  SpecType -> SpecType -> F.Expr -> CG ()
consRelCheck γ ψ (Tick _ e) d t s p =
  {- traceChk "Left Tick" e d t s p $ -} consRelCheck γ ψ e d t s p

consRelCheck γ ψ e (Tick _ d) t s p =
  {- traceChk "Right Tick" e d t s p $ -} consRelCheck γ ψ e d t s p

-- consRelCheck γ ψ l1@(Lam α1 e1) l2@(Lam α2 e2) rt1@(RAllT s1 t1 r1) rt2@(RAllT s2 t2 r2) p
--   = traceChk "Lam Type" l1 l2 rt1 rt2 p $ do
--     entlFunRefts γ ψ r1 r2
--     γ' <- γ `extendWithTyVar` α1
--     γ'' <- γ' `extendWithTyVar` α2
--     consRelCheck γ'' ψ e1 e2 (sub (s1, α1) t1) (sub (s2, α2) t2) p
--   where sub (α', α) = subsTyVar_meet' (ty_var_value α', rVar α)

consRelCheck γ ψ l1@(Lam x1 e1) l2@(Lam x2 e2) rt1@(RFun v1 s1 t1 r1) rt2@(RFun v2 s2 t2 r2) pr@(F.PImp q p)
  = traceChk "Lam Expr" l1 l2 rt1 rt2 pr $ do
    entlFunRefts γ ψ r1 r2
    let (evar1, evar2) = mkRelCopies x1 x2
    let (e1', e2')     = subRelCopies e1 x1 e2 x2
    let (pvar1, pvar2) = (F.symbol evar1, F.symbol evar2)
    γ'  <- γ += ("consRelCheck Lam L", pvar1, s1)
    γ'' <- γ' += ("consRelCheck Lam R", pvar2, s2)
    let p'    = unapplyRelArgs v1 v2 p
    let subst = F.subst $ F.mkSubst [(v1, F.EVar pvar1), (v2, F.EVar pvar2)]
    consRelCheck γ'' (subst q : ψ) e1' e2' (subst t1) (subst t2) (subst p')

consRelCheck γ ψ l1@(Let (NonRec x1 d1) e1) l2@(Let (NonRec x2 d2) e2) t1 t2 p = 
  traceChk "Let" l1 l2 t1 t2 p $ do
  (s1, s2, q) <- consRelSynth γ ψ d1 d2
  let (evar1, evar2) = mkRelCopies x1 x2
  let (e1', e2') = subRelCopies e1 x1 e2 x2
  γ' <- γ += ("consRelCheck Let L", F.symbol evar1, s1)
  γ'' <- γ' += ("consRelCheck Let R", F.symbol evar2, s2)
  consRelCheck γ'' (q:ψ) e1' e2' t1 t2 p

consRelCheck γ ψ c1@(Case e1 x1 _ alts1) c2@(Case e2 x2 _ alts2) t1 t2 p 
  | Just alts <- unifyAlts x1 x2 alts1 alts2 = 
  traceChk "Case" c1 c2 t1 t2 p $ do
  (s1, s2, _) <- consRelSynth γ ψ e1 e2
  γ' <- γ += ("consRelCheck Case L", x1', s1)
  γ'' <- γ' += ("consRelCheck Case R", x2', s2)
  forM_ (ctors alts) $ consSameCtors γ'' ψ x1' x2' s1 s2 (nonDefaults alts)
  forM_ alts $ consRelCheckAlt γ'' ψ t1 t2 p x1' x2' s1 s2
  where
    nonDefaults = filter (/= DEFAULT) . ctors
    ctors = map (\(c, _, _, _, _) -> c)
    (evar1, evar2) = mkRelCopies x1 x2
    x1' = F.symbol evar1
    x2' = F.symbol evar2
  
consRelCheck γ ψ e d t1 t2 p = 
  traceChk "Synth" e d t1 t2 p $ do
  (s1, s2, q) <- consRelSynth γ ψ e d
  let psubst = F.substf (matchFunArgs t1 s1) . F.substf (matchFunArgs t2 s2)
  consRelSub γ ψ s1 s2 q (psubst p)
  γψ <- γ `extendWithExprs` ψ
  addC (SubC γψ s1 t1) ("consRelCheck (Synth): s1 = " ++ F.showpp s1 ++ " t1 = " ++ F.showpp t1)
  addC (SubC γψ s2 t2) ("consRelCheck (Synth): s2 = " ++ F.showpp s2 ++ " t2 = " ++ F.showpp t2)

consSameCtors :: CGEnv -> PrEnv -> F.Symbol -> F.Symbol -> SpecType -> SpecType -> [AltCon] -> AltCon  -> CG ()
consSameCtors γ ψ x1 x2 s1 s2 alts (DataAlt c) | c == Ghc.trueDataCon || c == Ghc.falseDataCon
  = entl γ ψ (F.PIff (F.EVar x1) (F.EVar x2)) "consSameCtors DataAlt Bool"
consSameCtors γ ψ x1 x2 s1 s2 alts (DataAlt c)
  = entl γ ψ (F.PIff (isCtor c $ F.EVar x1) (isCtor c $ F.EVar x2)) "consSameCtors DataAlt"
consSameCtors γ ψ x1 x2 _ _ _ (LitAlt l)
  = F.panic "consSameCtors undefined for literals"
consSameCtors _ _ _ _ _ _ alts DEFAULT
  = F.panic "consSameCtors undefined for default"

isCtor :: Ghc.DataCon -> F.Expr -> F.Expr
isCtor d = F.EApp (F.EVar $ makeDataConChecker d)

consRelCheckAlt :: CGEnv -> PrEnv -> SpecType -> SpecType -> F.Expr -> 
  F.Symbol -> F.Symbol -> SpecType -> SpecType -> RelAlt -> CG ()
consRelCheckAlt γ ψ t1 t2 p x1 x2 s1 s2 (c, bs1, bs2, e1, e2) = do
  ct1 <- ctorTy γ c s1 
  ct2 <- ctorTy γ c s2
  γ'  <- unapply γ x1 s1 bs1 ct1 
  γ'' <- unapply γ' x2 s2 bs2 ct2
  consRelCheck γ'' ψ e1 e2 t1 t2 p

ctorTy :: CGEnv -> AltCon -> SpecType -> CG SpecType
ctorTy γ (DataAlt c) (RApp _ ts _ _) 
  | Just ct <- mbct = refreshTy $ ct `instantiateTys` ts
  | Nothing <- mbct = F.panic $ "ctorTy: data constructor out of scope" ++ F.showpp c
  where mbct = γ ?= F.symbol (dataConWorkId c)
ctorTy _ (DataAlt _) t =
  F.panic $ "ctorTy: type " ++ F.showpp t ++ " doesn't have top-level data constructor"
ctorTy _ (LitAlt c) _ = return $ uTop <$> literalFRefType c
ctorTy _ DEFAULT t = return t

unapply :: CGEnv -> F.Symbol -> SpecType -> [Var] -> SpecType -> CG CGEnv
unapply γ y yt (z : zs) (RFun x s t _) = do
  let evar = F.symbol z
  γ' <- γ += ("unapply arg", evar, s)
  unapply γ' y yt zs (t `F.subst1` (x, F.EVar evar))
unapply _ _ _ (_ : _) t = F.panic $ "can't unapply type " ++ F.showpp t
unapply γ y yt [] t = γ += ("unapply res", y, t `F.meet` yt)

instantiateTys :: SpecType -> [SpecType] -> SpecType
instantiateTys = L.foldl' go
 where
  go (RAllT α tbody _) t = subsTyVar_meet' (ty_var_value α, t) tbody
  go tbody             t = 
    F.panic $ "instantiateTys: non-polymorphic type " ++ F.showpp tbody ++ " to instantiate with " ++ F.showpp t 

--------------------------------------------------------------
-- Core Synthesis Rules --------------------------------------
--------------------------------------------------------------

consRelSynth :: CGEnv -> PrEnv -> CoreExpr -> CoreExpr -> CG (SpecType, SpecType, F.Expr)
consRelSynth γ ψ (Tick _ e) d =
  {- traceSyn "Left Tick" e d -} consRelSynth γ ψ e d

consRelSynth γ ψ e (Tick _ d) =
  {- traceSyn "Right Tick" e d -} consRelSynth γ ψ e d

consRelSynth γ ψ a1@(App e1 d1) a2@(App e2 d2) =
    traceSyn "App" a1 a2 $ do
    (ft1, ft2, p) <- consRelSynth γ ψ e1 e2
    consRelSynthApp γ ψ ft1 ft2 p (GM.unTickExpr d1) (GM.unTickExpr d2)  
 
consRelSynth γ _ e d = do
  t <- consUnarySynth γ e >>= refreshTy
  s <- consUnarySynth γ d >>= refreshTy
  return (t, s, wfTruth t s)

consRelSynthApp :: CGEnv -> PrEnv -> SpecType -> SpecType -> 
  F.Expr -> CoreExpr -> CoreExpr -> CG (SpecType, SpecType, F.Expr)
consRelSynthApp γ ψ (RAllT α1 ft1 r1) (RAllT α2 ft2 r2) p (Type t1) (Type t2) = do
  entlFunRefts γ ψ r1 r2
  t1' <- trueTy t1
  t2' <- trueTy t2
  return (subsTyVar_meet' (ty_var_value α1, t1') ft1, subsTyVar_meet' (ty_var_value α2, t2') ft2, p)
consRelSynthApp γ ψ (RFun v1 s1 t1 r1) (RFun v2 s2 t2 r2) (F.PImp q p) d1@(Var x1) d2@(Var x2) = do
  entlFunRefts γ ψ r1 r2
  let qsubst = F.subst $ F.mkSubst [(v1, F.EVar resL), (v2, F.EVar resR)]
  consRelCheck γ ψ d1 d2 s1 s2 (qsubst q)
  let subst = F.subst $ F.mkSubst [(v1, F.EVar $ F.symbol x1), (v2, F.EVar $ F.symbol x2)]
  return (subst t1, subst t2, subst $ unapplyRelArgs v1 v2 p)
consRelSynthApp _ _ t1 t2 p d1 d2 = 
  F.panic $ "consRelSynthApp: malformed function types or predicate for arguments " ++ F.showpp (t1, t2, p, d1, d2)

--------------------------------------------------------------
-- Unary Rules -----------------------------------------------
--------------------------------------------------------------

consUnarySynth :: CGEnv -> CoreExpr -> CG SpecType
consUnarySynth γ (Tick _ e) = consUnarySynth γ e
consUnarySynth γ (Var x) =
  case γ ?= F.symbol x of
    Just t -> return $ selfify t x
    Nothing -> F.panic $ "consUnarySynth (Var) " ++ F.showpp x ++ " not in scope " ++ F.showpp γ
consUnarySynth _ (Lit c) = return $ uRType $ literalFRefType c
consUnarySynth γ e@(Let _ _) = do
  t   <- freshTy_type LetE e $ exprType e
  addW $ WfC γ t
  consUnaryCheck γ e t
  return t
consUnarySynth γ (App e d) = do
  et <- consUnarySynth γ e
  consUnarySynthApp γ et (GM.unTickExpr d)
consUnarySynth γ e@(Lam x d) = do
  let FunTy { ft_arg = s' } = exprType e
  s      <- freshTy_type LamE (Var x) s'
  γ'      <- γ += ("consUnarySynth (Lam)", F.symbol x, s)
  t       <- consUnarySynth γ' d
  addW     $ WfC γ t
  return   $ RFun (F.symbol x) s t mempty
consUnarySynth _ e@(Case _ _ _ _) = F.panic $ "consUnarySynth is undefined for Case " ++ F.showpp e
consUnarySynth _ e@(Cast _ _) = F.panic $ "consUnarySynth is undefined for Cast " ++ F.showpp e
consUnarySynth _ e@(Type _) = F.panic $ "consUnarySynth is undefined for Type " ++ F.showpp e
consUnarySynth _ e@(Coercion _) = F.panic $ "consUnarySynth is undefined for Coercion " ++ F.showpp e

selfify :: F.Symbolic a => SpecType -> a -> SpecType
selfify t@(RApp {}) x = t `strengthen` eq x  
  where eq = uTop . F.symbolReft . F.symbol
selfify t _ = t

consUnarySynthApp :: CGEnv -> SpecType -> CoreExpr -> CG SpecType
consUnarySynthApp γ (RFun x s t _) d@(Var y) = do
  consUnaryCheck γ d s
  return $ t `F.subst1` (x, F.EVar $ F.symbol y)
consUnarySynthApp _ (RAllT α t _) (Type s) = do
    s' <- trueTy s
    return $ subsTyVar_meet' (ty_var_value α, s') t
consUnarySynthApp _ ft d = 
  F.panic $ "consUnarySynthApp malformed function type " ++ F.showpp ft ++
            " for argument " ++ F.showpp d  

consUnaryCheck :: CGEnv -> CoreExpr -> SpecType -> CG ()
consUnaryCheck γ (Let (NonRec x d) e) t = do
  s <- consUnarySynth γ d
  γ' <- γ += ("consUnaryCheck Let", F.symbol x, s)
  consUnaryCheck γ' e t
consUnaryCheck γ e t = do
  s <- consUnarySynth γ e
  addC (SubC γ s t) ("consUnaryCheck (Synth): s = " ++ F.showpp s ++ " t = " ++ F.showpp t)

--------------------------------------------------------------
-- Predicate Subtyping  --------------------------------------
--------------------------------------------------------------

consRelSub :: CGEnv -> PrEnv -> SpecType -> SpecType -> F.Expr -> F.Expr -> CG ()
consRelSub γ ψ f1@(RFun x1 s1 e1 _) f2 p1 p2 =
  traceSub "fun" f1 f2 p1 p2 $ do
    γ' <- γ += ("consRelSub RFun L", F.symbol x1, s1)
    let psubst = unapplyArg resL x1
    consRelSub γ' ψ e1 f2 (psubst p1) (psubst p2)
consRelSub γ ψ f1 f2@(RFun x2 s2 e2 _) p1 p2 = 
  traceSub "fun" f1 f2 p1 p2 $ do
    γ' <- γ += ("consRelSub RFun R", F.symbol x2, s2)
    let psubst = unapplyArg resR x2
    consRelSub γ' ψ f1 e2 (psubst p1) (psubst p2)
consRelSub γ ψ t1@RApp {} t2@RApp {} p1 p2 = 
  traceSub "base" t1 t2 p1 p2 $ do
  γ' <- γ += ("consRelSub Base L", resL, t1) 
  γ'' <- γ' += ("consRelSub Base R", resR, t2)
  entl γ'' ψ (F.PImp p1 p2) "consRelSub Base"
consRelSub _ _ t1@(RVar _ _) t2@(RVar _ _) _ _ = F.panic $ "consRelSub is undefined for RVar " ++ show (t1, t2)
consRelSub _ _ t1@(RHole _) t2@(RHole _) _ _ = F.panic $ "consRelSub is undefined for RHole " ++ show (t1, t2)
consRelSub _ _ t1@(RExprArg _) t2@(RExprArg _) _ _ = F.panic $ "consRelSub is undefined for RExprArg " ++ show (t1, t2)
consRelSub _ _ t1@REx {} t2@REx {} _ _ = F.panic $ "consRelSub is undefined for REx " ++ show (t1, t2)
consRelSub _ _ t1@RAllE {} t2@RAllE {} _ _ = F.panic $ "consRelSub is undefined for RAllE " ++ show (t1, t2)
consRelSub _ _ t1@RRTy {} t2@RRTy {} _ _ = F.panic $ "consRelSub is undefined for RRTy " ++ show (t1, t2)
consRelSub _ _ t1@RAllP {} t2@RAllP {} _ _ = F.panic $ "consRelSub is undefined for RAllP " ++ show (t1, t2)
consRelSub _ _ t1@RAllT {} t2@RAllT {} _ _ = F.panic $ "consRelSub is undefined for RAllT " ++ show (t1, t2)
consRelSub _ _ t1@RImpF {} t2@RImpF {} _ _ = F.panic $ "consRelSub is undefined for RImpF " ++ show (t1, t2)
consRelSub _ _ t1 t2 _ _ =  F.panic $ "consRelSub is undefined for different types " ++ show (t1, t2)

--------------------------------------------------------------
-- Predicate Well-Formedness ---------------------------------
--------------------------------------------------------------

wfTruth :: SpecType -> SpecType -> F.Expr
wfTruth (RAllT _ t1 _) (RAllT _ t2 _) = wfTruth t1 t2
wfTruth (RFun _ _ t1 _) (RFun _ _ t2 _) = 
  F.PImp F.PTrue $ wfTruth t1 t2
wfTruth _ _ = F.PTrue

--------------------------------------------------------------
-- Helper Definitions ----------------------------------------
--------------------------------------------------------------

extendWithTyVar :: CGEnv -> TyVar -> CG CGEnv
extendWithTyVar γ a
  | isValKind (tyVarKind a) 
  = γ += ("extendWithTyVar", F.symbol a, kindToRType $ tyVarKind a)
  | otherwise 
  = return γ

unifyAlts :: CoreBndr -> CoreBndr -> [Alt CoreBndr] -> [Alt CoreBndr] -> Maybe [RelAlt]
unifyAlts x1 x2 alts1 alts2 = mapM subRelCopiesAlts (zip alts1 alts2)
  where 
    subRelCopiesAlts ((a1, bs1, e1), (a2, bs2, e2)) 
      | a1 /= a2  = Nothing
      | otherwise = let (e1', e2') = L.foldl' sub (subRelCopies e1 x1 e2 x2) (zip bs1 bs2)
                     in Just (a1, mkLCopies bs1, mkRCopies bs2, e1', e2')
    sub (e1, e2) (x1, x2) = subRelCopies e1 x1 e2 x2

matchFunArgs :: SpecType -> SpecType -> F.Symbol -> F.Expr
matchFunArgs (RAllT _ t1 _) t2 x = matchFunArgs t1 t2 x
matchFunArgs t1 (RAllT _ t2 _) x = matchFunArgs t1 t2 x
matchFunArgs (RFun x1 _ t1 _) (RFun x2 _ t2 _) x = 
  if x == x1 then F.EVar x2 else matchFunArgs t1 t2 x
matchFunArgs RApp {} RApp {} x = F.EVar x
matchFunArgs t1 t2 _ = F.panic $ "matchFunArgs undefined for " ++ F.showpp (t1, t2)

entl :: CGEnv -> PrEnv -> F.Expr -> String -> CG ()
entl γ ψ p msg = do
  γψ <- γ `extendWithExprs` ψ
  addC (SubR γψ ORel $ uReft (F.vv_, F.PIff (F.EVar F.vv_) p)) msg

entlFunRefts :: CGEnv -> [F.Expr] -> RReft -> RReft -> CG ()
entlFunRefts γ ψ r1 r2 = do
  entl γ ψ (F.reftPred $ ur_reft r1) "entlFunRefts L"
  entl γ ψ (F.reftPred $ ur_reft r2) "entlFunRefts R"  

subRelCopies :: CoreExpr -> Var -> CoreExpr -> Var -> (CoreExpr, CoreExpr)
subRelCopies e1 x1 e2 x2 = 
  (sub (M.singleton x1 $ Var evar1) e1, sub (M.singleton x2 $ Var evar2) e2)
  where (evar1, evar2) = mkRelCopies x1 x2

mkRelCopies :: Var -> Var -> (Var, Var)
mkRelCopies x1 x2 = (mkCopyWithSuffix "l" x1, mkCopyWithSuffix "r" x2)

mkLCopies :: [Var] -> [Var]
mkLCopies = (mkCopyWithSuffix "l" <$>)

mkRCopies :: [Var] -> [Var]
mkRCopies = (mkCopyWithSuffix "r" <$>)

mkCopyWithName :: String -> Var -> Var
mkCopyWithName s v = 
  Ghc.setVarName v $ Ghc.mkSystemName (Ghc.getUnique v) (Ghc.mkVarOcc s)

mkCopyWithSuffix :: String -> Var -> Var
mkCopyWithSuffix s v = mkCopyWithName (Ghc.getOccString v ++ s) v

findBody :: Var -> [CoreBind] -> CoreExpr
findBody x bs = case lookup x (concatMap binds bs) of
                 Nothing -> F.panic $ "Not found definition for " ++ show x
                 Just e  -> e
  where
    binds (NonRec x e) = [(x,e)]
    binds (Rec xes)    = xes

extendWithExprs :: CGEnv -> [F.Expr] -> CG CGEnv 
extendWithExprs γ es = do
  dummy <- fresh
  let reft = uReft (F.vv_, F.PAnd es)
  γ += ("extend with predicate env", dummy, RVar (symbolRTyVar F.dummySymbol) reft)

unapplyArg :: F.Symbol -> F.Symbol -> F.Expr -> F.Expr
unapplyArg f y e = F.mapExpr sub e
  where 
    sub :: F.Expr -> F.Expr
    sub (F.EApp (F.EVar r) (F.EVar x)) 
      | r == f && x == y = F.EVar r
    sub e = e

unapplyRelArgs :: F.Symbol -> F.Symbol -> F.Expr -> F.Expr
unapplyRelArgs x1 x2 = unapplyArg resL x1 . unapplyArg resR x2

--------------------------------------------------------------
-- Debug -----------------------------------------------------
--------------------------------------------------------------

traceUnapply
  :: (PPrint x1, PPrint x2, PPrint e1, PPrint e2)
  => x1 -> x2 -> e1 -> e2 -> e2
traceUnapply x1 x2 e1 e2 = D.trace ("Unapply\n"
                      ++ "x1: " ++ F.showpp x1 ++ "\n\n"
                      ++ "x2: " ++ F.showpp x2 ++ "\n\n"
                      ++ "e1: " ++ F.showpp e1 ++ "\n\n"
                      ++ "e2: " ++ F.showpp e2) e2


traceSub 
  :: (PPrint t, PPrint s, PPrint p, PPrint q)
  => String -> t -> s -> p -> q -> a -> a
traceSub msg t s p q = D.trace (msg ++ " RelSub\n"
                      ++ "t: " ++ F.showpp t ++ "\n\n"
                      ++ "s: " ++ F.showpp s ++ "\n\n"
                      ++ "p: " ++ F.showpp p ++ "\n\n"
                      ++ "q: " ++ F.showpp q)


traceChk
  :: (PPrint e, PPrint d, PPrint t, PPrint s, PPrint p)
  => String -> e -> d -> t -> s -> p -> a -> a
traceChk expr = trace (expr ++ " To CHECK")

traceSyn
  :: (PPrint e, PPrint d) => String -> e -> d -> a -> a
traceSyn expr e d = trace (expr ++ " To SYNTH") e d F.PTrue F.PTrue F.PTrue

trace
  :: (PPrint e, PPrint d, PPrint t, PPrint s, PPrint p)
  => String -> e -> d -> t -> s -> p -> a -> a
trace msg e d t s p = D.trace (msg ++ "\n"
                      ++ "e: " ++ F.showpp e ++ "\n\n"
                      ++ "d: " ++ F.showpp d ++ "\n\n"
                      ++ "t: " ++ F.showpp t ++ "\n\n"
                      ++ "s: " ++ F.showpp s ++ "\n\n"
                      ++ "p: " ++ F.showpp p)
