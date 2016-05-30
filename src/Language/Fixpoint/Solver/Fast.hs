-- | This module contains the code for the new "fast" solver, that creates
--   bit-indexed propositions for each binder and constraint-id, links them
--   via the environment dominator tree, after which each lhsPred is simply
--   a conjunction of the RHS binder and the "current" solutions for dependent
--   (cut) KVars.

{-# LANGUAGE TypeOperators #-}

module Language.Fixpoint.Solver.Fast (

    -- * Constructor
      create

    -- * BackGround Predicate
    , backgroundPred

    -- * LHS Predicate
    , lhsPred

    ) where

import           Language.Fixpoint.Types.Config
import qualified Language.Fixpoint.Types            as F
import qualified Language.Fixpoint.Types.Solutions  as Sol
-- import qualified Data.HashMap.Strict                as M

--------------------------------------------------------------------------------
create :: Config -> F.SInfo a -> Sol.FastInfo
--------------------------------------------------------------------------------
create = error "TBD:Fast.create"

--------------------------------------------------------------------------------
backgroundPred :: Sol.FastInfo -> F.Pred
--------------------------------------------------------------------------------
backgroundPred = error "TBD:backgroundPred"

--------------------------------------------------------------------------------
lhsPred :: Sol.FastInfo -> F.SolEnv -> Sol.Solution -> F.SimpC a -> F.Expr
--------------------------------------------------------------------------------
lhsPred = undefined






{- | [NOTE: Bit-Indexed Representation]

     The whole constraint system will be represented by a collection
     of bit indexed propositions:

      b(i) <=> pred(i)

      where pred(i) encodes the logical refinement corresponding to i-th binder.
 -}
