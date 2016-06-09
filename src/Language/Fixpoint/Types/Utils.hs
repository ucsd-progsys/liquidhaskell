-- | This module has various utility functions for accessing queries.
--   TODO: move the "clients" in Visitors into this module.

module Language.Fixpoint.Types.Utils (
  -- * Domain of a kvar
    kvarDomain

  -- * Free variables in a refinement
  , reftFreeVars

  -- * Deconstruct a SortedReft
  , sortedReftConcKVars
  ) where

import qualified Data.HashMap.Strict                  as M
import qualified Data.HashSet                         as S
-- import           Data.Either (mapEither)

import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.Refinements
import           Language.Fixpoint.Types.Environments
import           Language.Fixpoint.Types.Constraints
import           Language.Fixpoint.Misc (mapEither, fst3)

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

--------------------------------------------------------------------------------
-- | Split a SortedReft into its concrete and KVar components
--------------------------------------------------------------------------------
sortedReftConcKVars :: Symbol -> SortedReft -> ([Pred], [KVSub])
sortedReftConcKVars x sr = mapEither exprKind es
  where
    es                   = [p `subst1` (v, eVar x) | Reft (v, p) <- rs ]
    rs                   = reftConjuncts $ sr_reft sr

exprKind :: Expr -> Either Expr KVSub
exprKind (PKVar k su) = Right (k, su)
exprKind p            = Left p
