-- | This module has various utility functions for accessing queries.
--   TODO: move the "clients" in Visitors into this module.

module Language.Fixpoint.Types.Utils (
  -- * Domain of a kvar
    kvarDomain

  -- * Free variables in a refinement
  , reftFreeVars
  ) where

-- import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Names
-- import           Language.Fixpoint.Types.Errors
-- import           Language.Fixpoint.Types.Spans
-- import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Types.Refinements
-- import           Language.Fixpoint.Types.Substitutions
import           Language.Fixpoint.Types.Environments
import           Language.Fixpoint.Types.Constraints
-- import           Language.Fixpoint.Types.Graphs

import           Language.Fixpoint.Misc (fst3)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S


--------------------------------------------------------------------------------
-- | Compute the domain of a kvar
--------------------------------------------------------------------------------
kvarDomain :: SInfo a -> KVar -> [Symbol]
--------------------------------------------------------------------------------
kvarDomain si k = domain (bs si) (getWfC si k)

domain :: BindEnv -> WfC a -> [Symbol]
domain be wfc = fst3 (wrft wfc) : map fst (envCs be $ wenv wfc)

getWfC :: SInfo a -> KVar -> WfC a
getWfC si k = ws si M.! k

--------------------------------------------------------------------------------
-- | Free variables of a refinement
--------------------------------------------------------------------------------
--TODO deduplicate (also in Solver/UniqifyBinds)
reftFreeVars :: Reft -> S.HashSet Symbol
reftFreeVars r@(Reft (v, _)) = S.delete v $ S.fromList $ syms r
