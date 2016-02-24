-- | This module re-exports the data types, operations and
--   serialization functions for representing Fixpoint's
--   implication (i.e. subtyping) and well-formedness
--   constraints.

module Language.Fixpoint.Types (
    module Language.Fixpoint.Types.PrettyPrint
  , module Language.Fixpoint.Types.Spans
  , module Language.Fixpoint.Types.Errors
  , module Language.Fixpoint.Types.Names
  , module Language.Fixpoint.Types.Sorts
  , module Language.Fixpoint.Types.Refinements
  , module Language.Fixpoint.Types.Substitutions
  , module Language.Fixpoint.Types.Environments
  , module Language.Fixpoint.Types.Constraints
  , module Language.Fixpoint.Types.Graphs
  , module Language.Fixpoint.Types.Utils
  ) where

import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Types.Spans
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Types.Refinements
import           Language.Fixpoint.Types.Substitutions
import           Language.Fixpoint.Types.Environments
import           Language.Fixpoint.Types.Constraints
import           Language.Fixpoint.Types.Graphs

import           Language.Fixpoint.Misc (fst3)
import qualified Data.HashMap.Strict as M


--------------------------------------------------------------------------------
-- | Compute the domain of a kvar
--------------------------------------------------------------------------------

kvarDomain :: SInfo a -> KVar -> [Symbol]
kvarDomain si k = domain (bs si) (getWfC si k)
  where
    domain :: BindEnv -> WfC a -> [Symbol]
    domain be wfc = fst3 (wrft wfc) : map fst (envCs be $ wenv wfc)

    getWfC :: SInfo a -> KVar -> WfC a
    getWfC si k = ws si M.! k
