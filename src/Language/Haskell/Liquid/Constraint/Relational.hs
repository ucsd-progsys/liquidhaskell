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

consRelTop :: Config -> TargetInfo -> CGEnv
          -> (Var, Var, LocSpecType, LocSpecType, F.Expr) -> CG ()
consRelTop _ ti γ (x,y,t,s,p) = do
  let cbs = giCbs $ giSrc ti
  let e = findBody x cbs
  let d = findBody y cbs
  let e' = traceChk "Init" e d t s p e
  consRelCheck γ [] e' d (val t) (val s) p

--------------------------------------------------------------
-- Core Checking Rules ---------------------------------------
--------------------------------------------------------------

type PrEnv = [F.Expr] 

-- Definition of CoreExpr: https://hackage.haskell.org/package/ghc-8.10.1/docs/CoreSyn.html
consRelCheck :: CGEnv -> PrEnv
        -> CoreExpr -> CoreExpr -> SpecType -> SpecType -> F.Expr -> CG ()
consRelCheck γ ψ (Tick _ e) d t s p =
  traceChk "Left Tick" e d t s p $ consRelCheck γ ψ e d t s p

consRelCheck γ ψ e (Tick _ d) t s p =
  traceChk "Right Tick" e d t s p $ consRelCheck γ ψ e d t s p

consRelCheck γ ψ l1@(Lam x1 e) l2@(Lam x2 d) rt1@(RFun v1 s1 t1 _) rt2@(RFun v2 s2 t2 _) pr@(F.PImp q p) = 
  traceChk "Lam" l1 l2 rt1 rt2 pr $ do
  let fresh1 = Ghc.getOccString x1 ++ "l"
  let fresh2 = Ghc.getOccString x2 ++ "r"
  let evar1 = copyVarWithName fresh1 x1
  let evar2 = copyVarWithName fresh2 x2
  let pvar1 = F.symbol evar1
  let pvar2 = F.symbol evar2
  γ' <- γ += ("consRelCheck Lam", pvar1, s1)
  γ'' <- γ' += ("consRelCheck Lam", pvar2, s2)
  let esubst = sub $ M.fromList [(x1, Var evar1), (x2, Var evar2)]
  let psubst = F.subst $ F.mkSubst [(v1, F.EVar pvar1), (v2, F.EVar pvar2)]
  consRelCheck γ'' (q:ψ) (esubst e) (esubst d) (psubst t1) (psubst t2) ({- r1 v1 := r1; r2 v2 := r2 -} psubst p)

consRelCheck γ ψ l1@(Let (NonRec x1 d1) e1) l2@(Let (NonRec x2 d2) e2) t1 t2 p = 
  traceChk "Let" l1 l2 t1 t2 p $ do
  (s1, s2, q) <- consRelSynth γ ψ d1 d2
  γ' <- γ += ("consRelCheck Let", F.symbol x1, s1)
  γ'' <- γ' += ("consRelCheck Let", F.symbol x2, s2)
  consRelCheck γ'' (q:ψ) e1 e2 t1 t2 p

consRelCheck γ ψ e d t1 t2 p = 
  traceChk "Synth" e d t1 t2 p $ do
  (s1, s2, q) <- consRelSynth γ ψ e d
  consRelSub γ ψ s1 s2 q p
  addC (SubC γ {- TODO: add psi to gamma -} s1 t1) ("consRelCheck (Synth): " ++ "s1 = " ++ F.showpp s1 ++ " t1 = " ++ F.showpp t1)
  addC (SubC γ {- TODO: add psi to gamma -} s2 t2) ("consRelCheck (Synth): " ++ "s2 = " ++ F.showpp s2 ++ " t2 = " ++ F.showpp t2)

--------------------------------------------------------------
-- Core Synthesis Rules --------------------------------------
--------------------------------------------------------------

consRelSynth :: CGEnv -> PrEnv
  -> CoreExpr -> CoreExpr -> CG (SpecType, SpecType, F.Expr)
consRelSynth γ ψ (Tick _ e) d =
  traceSyn "Left Tick" e d $ consRelSynth γ ψ e d

consRelSynth γ ψ e (Tick _ d) =
  traceSyn "Right Tick" e d $ consRelSynth γ ψ e d

consRelSynth γ ψ a1@(App e1 d1) a2@(App e2 d2) =
  traceSyn "App" a1 a2 $ do
    syn <- consRelSynth γ ψ e1 e2
    case syn of 
      (RFun v1 s1 t1 _, RFun v2 s2 t2 _, F.PImp q p) -> do 
        consRelCheck γ ψ d1 d2 s1 s2 ({- subst -} q)
        return (t1, t2, p)
      _ -> F.panic $ "consRelSynth: malformed types or predicate for function application " ++ F.showpp syn

consRelSynth γ _ e d = do
  t <- consUnarySynth γ e
  s <- consUnarySynth γ d
  return (t, s, wfTruth t s)

--------------------------------------------------------------
-- Unary Rules -----------------------------------------------
--------------------------------------------------------------

consUnarySynth :: CGEnv -> CoreExpr -> CG SpecType
consUnarySynth γ (Var x) =
  case γ ?= F.symbol x of
    Just t -> return t
    Nothing -> F.panic $ "consUnarySynth Var " ++ F.showpp x ++ " not in scope " ++ F.showpp γ 

--------------------------------------------------------------
-- Predicate Subtyping  --------------------------------------
--------------------------------------------------------------

consRelSub :: CGEnv -> PrEnv -> SpecType -> SpecType -> F.Expr -> F.Expr -> CG ()
consRelSub γ ψ f1@(RFun x1 s1 t1 _) f2@(RFun x2 s2 t2 _) p1 p2 = 
  do
    γ' <- γ += ("consRelSub RFun", F.symbol x1, s1)
    γ'' <- γ' += ("consRelSub RFun", F.symbol x2, s2)
    consRelSub γ'' ψ f1 f2 ({- r1 x1 := r1; r2 x2 := r2 -} p1) ({- r1 x1 := r1; r2 x2 := r2 -} p2)
consRelSub γ ψ t1 t2 p1 p2 = do
  γ' <- γ += ("consRelSub Base", fromString "r1", t1) 
  γ'' <- γ' += ("consRelSub Base", fromString "r2", t2) 
  addC (SubR γ'' {- TODO: add psi to gamma -} OInv $ uReft (F.vv_, F.PImp p1 p2)) "consRelSub Base"
consRelSub γ ψ t1 t2 p1 p2 = F.panic "consRelSub undefined"

--------------------------------------------------------------
-- Predicate Well-Formedness ---------------------------------
--------------------------------------------------------------

wfTruth :: SpecType -> SpecType -> F.Expr
wfTruth RFun { rt_out = t1 } RFun { rt_out = t2 } = 
  F.PImp F.PTrue $ wfTruth t1 t2
wfTruth _ _ = F.PTrue

--------------------------------------------------------------
-- Helper Definitions ----------------------------------------
--------------------------------------------------------------

copyVarWithName :: String -> Var -> Var
copyVarWithName s v = 
  Ghc.setVarName v $ Ghc.mkSystemName (Ghc.getUnique v) (Ghc.mkVarOcc s)

varNameString :: Var -> String
varNameString = Ghc.getOccString

findBody :: Var -> [CoreBind] -> CoreExpr
findBody x bs = case lookup x (concatMap binds bs) of
                 Nothing -> F.panic $ "Not found definition for " ++ show x
                 Just e  -> e
  where
    binds (NonRec x e) = [(x,e)]
    binds (Rec xes)    = xes

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
