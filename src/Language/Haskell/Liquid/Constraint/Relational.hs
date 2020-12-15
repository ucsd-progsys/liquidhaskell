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
import qualified Data.Foldable                                  as F
import qualified Data.Functor.Identity
import qualified Data.HashMap.Strict                            as M
import qualified Data.HashSet                                   as S
import qualified Data.List                                      as L
import           Data.Maybe                                     (catMaybes,
                                                                 fromMaybe,
                                                                 isJust)
import qualified Data.Traversable                               as T
import qualified Debug.Trace as D
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
          -> (Var, Var, LocSpecType, LocSpecType, F.Expr) -> CG ()
consRelTop _ ti γ (x,y,t,s,p) = do
  let cbs = giCbs $ giSrc ti
  let e = findBody x cbs
  let d = findBody y cbs
  let e' = traceChk "Init" e d t s p e
  consRelChk γ [] e' d (val t) (val s) p

--------------------------------------------------------------
-- Core Checking Rules ---------------------------------------
--------------------------------------------------------------

-- Definition of CoreExpr: https://hackage.haskell.org/package/ghc-8.10.1/docs/CoreSyn.html
consRelChk :: CGEnv -> [F.Expr]
        -> CoreExpr -> CoreExpr -> SpecType -> SpecType -> F.Expr -> CG ()
consRelChk γ ψ (Tick _ e) d t s p =
  traceChk "Left Tick" e d t s p $ consRelChk γ ψ e d t s p

consRelChk γ ψ e (Tick _ d) t s p = 
  traceChk "Right Tick" e d t s p $ consRelChk γ ψ e d t s p

consRelChk γ ψ l1@(Lam x e) l2@(Lam y d) rt1@(RFun u s1 t1 _) rt2@(RFun v s2 t2 _) pr@(F.PAll [_,_] (F.PImp q p)) 
  | not (isTyVar x) && not (isTyVar y) = do
  γ' <- γ += ("consRelChk Lam", F.symbol x, s1)
  γ'' <- γ' += ("consRelChk Lam", F.symbol y, s2)
  traceChk "Lam" l1 l2 rt1 rt2 pr $ 
    consRelChk γ ψ ({- subst -} e) ({- subst -} d) t1 t2 ({- subst -} p)

consRelChk γ ψ l1@(Let b1@(NonRec x1 d1) e1) l2@(Let b2@(NonRec x2 d2) e2) t1 t2 p = do
  (s1, s2, q) <- traceChk "Let" l1 l2 t1 t2 p $ consRelSyn γ ψ d1 d2
  γ' <- consCBLet γ b1
  γ'' <- consCBLet γ' b2
  consRelChk γ'' (q:ψ) e1 e2 t1 t2 p

consRelChk γ ψ e d t1 t2 p = do
  (s1, s2, q) <- traceChk "Syn" e d t1 t2 p $ consRelSyn γ ψ e d
  consRelSub γ ψ s1 s2 q p
  addC (SubC γ {- TODO: add psi to gamma -} s1 t1) ("consRelChk (Syn): " ++ "s1 = " ++ F.showpp s1 ++ " t1 = " ++ F.showpp t1)
  addC (SubC γ {- TODO: add psi to gamma -} s2 t2) ("consRelChk (Syn): " ++ "s2 = " ++ F.showpp s2 ++ " t2 = " ++ F.showpp t2)
  
consRelSyn :: CGEnv -> [F.Expr]
  -> CoreExpr -> CoreExpr -> CG (SpecType, SpecType, F.Expr)
consRelSyn γ ψ (Tick _ e) d =
  traceSyn "Left Tick" e d $ consRelSyn γ ψ e d 

consRelSyn γ ψ e (Tick _ d) =
  traceSyn "Right Tick" e d $ consRelSyn γ ψ e d

-- TODO: fix cyclic dependency on Language.Haskell.Liquid.Constraint.Generate
consRelSyn γ ψ e d = do
  t <- consE γ e
  s <- consE γ d
  return (t, s, F.PTrue)

consRelSyn γ ψ e d = F.panic $ "consRelSyn can't synth types and a predicate for " ++ show e ++ " and " ++ show d

--------------------------------------------------------------
-- TODO ------------------------------------------------------
--------------------------------------------------------------

consRelSub = undefined
consE = undefined
consCBLet = undefined

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
