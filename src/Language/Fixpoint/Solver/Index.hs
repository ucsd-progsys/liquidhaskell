-- | This module contains the code for the new "fast" solver, that creates
--   bit-indexed propositions for each binder and constraint-id, links them
--   via the environment dominator tree, after which each lhsPred is simply
--   a conjunction of the RHS binder and the "current" solutions for dependent
--   (cut) KVars.

{-# LANGUAGE TypeOperators #-}

module Language.Fixpoint.Solver.Index (

    -- * Constructor
      create

    -- * BackGround Predicate
    , backgroundPred

    -- * LHS Predicate
    , lhsPred

    ) where

import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types.Config
import qualified Language.Fixpoint.Types            as F
import           Language.Fixpoint.Types.Solutions
-- import qualified Data.HashMap.Strict                as M
import qualified Data.HashSet                       as S

--------------------------------------------------------------------------------
create :: Config -> F.SInfo a -> S.HashSet F.KVar -> Index
--------------------------------------------------------------------------------
create _cfg sI cKs = FastIdx
  { bindExpr = bE
  , kvUse    = kU
  , bindPrev = mkBindPrev sI
  , kvDef    = mkKvDef    sI
  , kvDeps   = mkKvDeps   sI cKs
  }
  where
    (bE, kU) = mkBindExpr sI

mkBindPrev :: F.SInfo a -> (F.BindId |-> F.BindId)
mkBindPrev = error "TBD:mkBindPrev"

mkBindExpr :: F.SInfo a -> (F.BindId |-> BindPred, KIndex |-> F.KVSub)
mkBindExpr = error "TBD:mkBindExpr"

mkKvDef :: F.SInfo a -> (F.KVar |-> Hyp)
mkKvDef = error "TBD:mkKvDef"

mkKvDeps :: F.SInfo a -> S.HashSet F.KVar -> (F.KVar |-> S.HashSet F.KVar)
mkKvDeps = error "TBD:mkKvDeps"

--------------------------------------------------------------------------------
backgroundPred :: Index -> F.Pred
--------------------------------------------------------------------------------
backgroundPred = error "TBD:backgroundPred"

--------------------------------------------------------------------------------
lhsPred :: Index -> F.SolEnv -> Solution -> F.SimpC a -> F.Expr
--------------------------------------------------------------------------------
lhsPred = undefined


{- | [NOTE: Bit-Indexed Representation]

     The whole constraint system will be represented by a collection
     of bit indexed propositions:

      b(i) <=> pred(i)

      where pred(i) encodes the logical refinement corresponding to i-th binder.
 -}
