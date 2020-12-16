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
import qualified Debug.Trace                                    as D
import           GHC.Stack
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types                        as F
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
import           Language.Haskell.Liquid.GHC.Play               (isHoleVar)
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
          -> (Var, Var, LocSpecType, LocSpecType, F.Pred) -> CG ()
consRelTop _ ti γ (x,y,t,s,p) = do
  let cbs = giCbs $ giSrc ti
  let e = findBody x cbs
  let d = findBody y cbs
  let sigs = gsTySigs $ gsSig $ giSpec ti
  let e'' = F.tracepp (F.showpp $ fixme sigs) e
  let e' = traceChk "Init" e d t s p e''
  consRelCheck γ [] e' d (val t) (val s) p
    where fixme = filter (F.isPrefixOfSym "Fixme" . F.symbol . fst)

--------------------------------------------------------------
-- Core Checking Rules ---------------------------------------
--------------------------------------------------------------

-- Definition of CoreExpr: https://hackage.haskell.org/package/ghc-8.10.1/docs/CoreSyn.html
consRelCheck :: CGEnv -> [F.Pred]
        -> CoreExpr -> CoreExpr -> SpecType -> SpecType -> F.Pred -> CG ()
consRelCheck γ ψ (Tick _ e) d t s p =
  traceChk "Left Tick" e d t s p $ consRelCheck γ ψ e d t s p

consRelCheck γ ψ e (Tick _ d) t s p =
  traceChk "Right Tick" e d t s p $ consRelCheck γ ψ e d t s p

consRelCheck γ ψ l1@(Lam x1 e) l2@(Lam x2 d) rt1@(RFun v1 s1 t1 _) rt2@(RFun v2 s2 t2 _) pr@(F.PImp q p) = 
  traceChk "Lam" l1 l2 rt1 rt2 pr $ do
  x1' <- fresh
  x2' <- fresh
  γ' <- γ += ("consRelCheck Lam", x1', s1)
  γ'' <- γ' += ("consRelCheck Lam", x2', s2)
  let subst = F.subst $ F.mkSubst [(v1, F.EVar x1'), (v2, F.EVar x2')]
  consRelCheck γ'' (q:ψ) ({- subst -} e) ({- subst -} d) (subst t1) (subst t2) ({- r1 v1 := r1; r2 v2 := r2 -} subst p)

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

consRelSynth :: CGEnv -> [F.Pred]
  -> CoreExpr -> CoreExpr -> CG (SpecType, SpecType, F.Pred)
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
  return (t, s, F.PTrue)

--------------------------------------------------------------
-- TODO ------------------------------------------------------
--------------------------------------------------------------

consRelSub = undefined

consUnarySynth :: CGEnv -> CoreExpr -> CG SpecType
consUnarySynth γ (Var x) =
  case γ ?= F.symbol x of
    Just t -> return t
    Nothing -> F.panic $ "consUnarySynth Var " ++ F.showpp x ++ " not in scope?"
--------------------------------------------------------------
-- Helper Definitions ----------------------------------------
--------------------------------------------------------------

findBody :: Var -> [CoreBind] -> CoreExpr
findBody x bs = case lookup x (concatMap binds bs) of
                 Nothing -> error ("Not found definition for " ++ show x)
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
