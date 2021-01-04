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

consRelTop 
  :: Config -> TargetInfo -> CGEnv -> (Var, Var, LocSpecType, LocSpecType, F.Expr) -> CG ()
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

resL, resR :: F.Symbol
resL = fromString "r1"
resR = fromString "r2"

-- Definition of CoreExpr: https://hackage.haskell.org/package/ghc-8.10.1/docs/CoreSyn.html
consRelCheck 
  :: CGEnv -> PrEnv -> CoreExpr -> CoreExpr -> SpecType -> SpecType -> F.Expr -> CG ()
consRelCheck γ ψ (Tick _ e) d t s p =
  {- traceChk "Left Tick" e d t s p $ -} consRelCheck γ ψ e d t s p

consRelCheck γ ψ e (Tick _ d) t s p =
  {- traceChk "Right Tick" e d t s p $ -} consRelCheck γ ψ e d t s p

consRelCheck γ ψ l1@(Lam x1 e1) l2@(Lam x2 e2) rt1@(RFun v1 s1 t1 _) rt2@(RFun v2 s2 t2 _) pr@(F.PImp q p) = 
  traceChk "Lam" l1 l2 rt1 rt2 pr $ do
  let evar1 = mkCopyWithSuffix "l" x1
  let evar2 = mkCopyWithSuffix "r" x2
  let pvar1 = F.symbol evar1
  let pvar2 = F.symbol evar2
  γ' <- γ += ("consRelCheck Lam L", pvar1, s1)
  γ'' <- γ' += ("consRelCheck Lam R", pvar2, s2)
  let e1' = sub (M.singleton x1 $ Var evar1) e1 
  let e2' = sub (M.singleton x2 $ Var evar2) e2
  let p' = unapplyRelArgs v1 v2 p
  let subst = F.subst $ F.mkSubst [(v1, F.EVar pvar1), (v2, F.EVar pvar2)]
  consRelCheck γ'' (subst q:ψ) e1' e2' (subst t1) (subst t2) (subst p')

consRelCheck γ ψ l1@(Let (NonRec x1 d1) e1) l2@(Let (NonRec x2 d2) e2) t1 t2 p = 
  traceChk "Let" l1 l2 t1 t2 p $ do
  (s1, s2, q) <- consRelSynth γ ψ d1 d2
  γ' <- γ += ("consRelCheck Let L", F.symbol x1, s1)
  γ'' <- γ' += ("consRelCheck Let R", F.symbol x2, s2)
  consRelCheck γ'' (q:ψ) e1 e2 t1 t2 p

consRelCheck γ ψ e d t1 t2 p = 
  traceChk "Synth" e d t1 t2 p $ do
  (s1, s2, q) <- consRelSynth γ ψ e d
  consRelSub γ ψ s1 s2 q p
  γψ <- γ `extendWithExprs` ψ
  addC (SubC γψ s1 t1) ("consRelCheck (Synth): " ++ "s1 = " ++ F.showpp s1 ++ " t1 = " ++ F.showpp t1)
  addC (SubC γψ s2 t2) ("consRelCheck (Synth): " ++ "s2 = " ++ F.showpp s2 ++ " t2 = " ++ F.showpp t2)

--------------------------------------------------------------
-- Core Synthesis Rules --------------------------------------
--------------------------------------------------------------

consRelSynth 
  :: CGEnv -> PrEnv -> CoreExpr -> CoreExpr -> CG (SpecType, SpecType, F.Expr)
consRelSynth γ ψ (Tick _ e) d =
  {- traceSyn "Left Tick" e d -} consRelSynth γ ψ e d

consRelSynth γ ψ e (Tick _ d) =
  {- traceSyn "Right Tick" e d  -} consRelSynth γ ψ e d

consRelSynth γ ψ a1@(App e1 d1) a2@(App e2 d2)
  | Type t1 <- GM.unTickExpr d1, Type t2 <- GM.unTickExpr d2 =
    traceSyn "App Expr Type" a1 a2 $ do
    syn <- consRelSynth γ ψ e1 e2
    case syn of 
      (RAllT α1 ft1 _, RAllT α2 ft2 _, p) -> do
        t1' <- trueTy t1
        t2' <- trueTy t2
        return (subsTyVar_meet' (ty_var_value α1, t1') ft1, subsTyVar_meet' (ty_var_value α2, t2') ft2, p)
      _ -> F.panic $ "consRelSynth TYPE: malformed types or predicate for function application " ++ F.showpp syn

consRelSynth γ ψ a1@(App e1 d1) a2@(App e2 d2)
  | Var x1 <- GM.unTickExpr d1, Var x2 <- GM.unTickExpr d2 =
    traceSyn "App Expr Var" a1 a2 $ do
      syn <- consRelSynth γ ψ e1 e2
      case syn of 
        (RFun v1 s1 t1 _, RFun v2 s2 t2 _, F.PImp q p) -> do
          let qsubst = F.subst $ F.mkSubst [(v1, F.EVar resL), (v2, F.EVar resR)]
          consRelCheck γ ψ d1 d2 s1 s2 (qsubst q)
          let subst = F.subst $ F.mkSubst [(v1, F.EVar $ F.symbol x1), (v2, F.EVar $ F.symbol x2)]
          return (subst t1, subst t2, subst $ unapplyRelArgs v1 v2 p)
        _ -> F.panic $ "consRelSynth VAR: malformed types or predicate for function application " ++ F.showpp syn
  | otherwise = 
    F.panic $ "conRelSynth: appliction of functions " ++ F.showpp (e1, e2) ++ 
              " to non-variable exprs " ++ F.showpp (d1, d2) 

consRelSynth γ _ e d = do
  t <- consUnarySynth γ e >>= refreshTy
  s <- consUnarySynth γ d >>= refreshTy
  return (t, s, wfTruth t s)

--------------------------------------------------------------
-- Unary Rules -----------------------------------------------
--------------------------------------------------------------

consUnarySynth :: CGEnv -> CoreExpr -> CG SpecType
consUnarySynth γ (Var x) =
  case γ ?= F.symbol x of
    Just t -> return t
    Nothing -> F.panic $ "consUnarySynth Var " ++ F.showpp x ++ " not in scope " ++ F.showpp γ 
consUnarySynth _ (Lit c) = 
  refreshVV $ uRType $ literalFRefType c
consUnarySynth _ e = F.panic $ "consUnarySynth is undefined for " ++ F.showpp e

--------------------------------------------------------------
-- Predicate Subtyping  --------------------------------------
--------------------------------------------------------------

consRelSub :: CGEnv -> PrEnv -> SpecType -> SpecType -> F.Expr -> F.Expr -> CG ()

consRelSub γ ψ f1@(RFun x1 s1 _ _) f2@(RFun x2 s2 _ _) p1 p2 = 
  traceSub "fun" f1 f2 p1 p2 $ do
    γ' <- γ += ("consRelSub RFun L", F.symbol x1, s1)
    γ'' <- γ' += ("consRelSub RFun R", F.symbol x2, s2)
    let psubst = unapplyRelArgs x1 x2
    consRelSub γ'' ψ f1 f2 (psubst p1) (psubst p2)

consRelSub γ ψ t1@RApp {} t2@RApp {} p1 p2 = 
  traceSub "base" t1 t2 p1 p2 $ do
  γ' <- γ += ("consRelSub Base L", resL, t1) 
  γ'' <- γ' += ("consRelSub Base R", resR, t2)
  γψ <- γ'' `extendWithExprs` ψ
  addC (SubR γψ ORel $ uReft (F.vv_, F.PIff (F.EVar F.vv_) $ F.PImp p1 p2)) "consRelSub Base"

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
  γ += ("extend with predicate env", F.vv_, RVar (symbolRTyVar dummy) reft)

unapplyRelArgs :: F.Symbol -> F.Symbol -> F.Expr -> F.Expr
unapplyRelArgs x1 x2 e = F.mapExpr sub e
  where 
    sub :: F.Expr -> F.Expr
    sub (F.EApp (F.EVar r) (F.EVar x)) 
      | r == resL && x == x1 = F.EVar r
      | r == resR && x == x2 = F.EVar r
    sub e = e

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
