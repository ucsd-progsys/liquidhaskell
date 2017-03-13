{-# LANGUAGE FlexibleContexts     #-}

-- | This module exports a single function that computes the dependency
-- information needed to eliminate non-cut KVars, and then transitively
-- collapse the resulting constraint dependencies.
-- See the type of `SolverInfo` for details.

module Language.Fixpoint.Solver.Eliminate (solverInfo) where

import qualified Data.HashSet        as S
import qualified Data.HashMap.Strict as M

import           Language.Fixpoint.Types.Config    (Config)
import qualified Language.Fixpoint.Types.Solutions as Sol
import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Visitor   (kvars, isConcC)
import           Language.Fixpoint.Graph
import           Language.Fixpoint.Misc            (safeLookup, group, errorstar)
import           Language.Fixpoint.Solver.Sanitize

--------------------------------------------------------------------------------
-- | `solverInfo` constructs a `SolverInfo` comprising the Solution and various
--   indices needed by the worklist-based refinement loop
--------------------------------------------------------------------------------
solverInfo :: Config -> SInfo a -> SolverInfo a b
--------------------------------------------------------------------------------
solverInfo cfg sI = SI sHyp sI' cD cKs
  where
    cD             = elimDeps     sI es nKs
    sI'            = cutSInfo     sI kI cKs
    sHyp           = Sol.fromList sE mempty mempty kHyps kS
    kHyps          = nonCutHyps   sI kI nKs
    kI             = kIndex       sI
    (es, cKs, nKs) = kutVars cfg  sI
    kS             = kvScopes     sI es
    sE             = symbolEnv   cfg sI


--------------------------------------------------------------------------------
kvScopes :: SInfo a -> [CEdge] -> M.HashMap KVar IBindEnv
kvScopes sI es = is2env <$> kiM
  where
    is2env = foldr1 intersectionIBindEnv . fmap (senv . getSubC sI)
    kiM    = group $ [(k, i) | (Cstr i, KVar k) <- es ] ++
                     [(k, i) | (KVar k, Cstr i) <- es ]

--------------------------------------------------------------------------------

cutSInfo :: SInfo a -> KIndex -> S.HashSet KVar -> SInfo a
cutSInfo si kI cKs = si { ws = ws', cm = cm' }
  where
    ws'   = M.filterWithKey (\k _ -> S.member k cKs) (ws si)
    cm'   = M.filterWithKey (\i c -> S.member i cs || isConcC c) (cm si)
    cs    = S.fromList      (concatMap kCs cKs)
    kCs k = M.lookupDefault [] k kI

kutVars :: Config -> SInfo a -> ([CEdge], S.HashSet KVar, S.HashSet KVar)
kutVars cfg si   = (es, depCuts ds, depNonCuts ds)
  where
    (es, ds)     = elimVars cfg si

--------------------------------------------------------------------------------
-- | Map each `KVar` to the list of constraints on which it appears on RHS
--------------------------------------------------------------------------------
type KIndex = M.HashMap KVar [Integer]

--------------------------------------------------------------------------------
kIndex     :: SInfo a -> KIndex
--------------------------------------------------------------------------------
kIndex si  = group [(k, i) | (i, c) <- iCs, k <- rkvars c]
  where
    iCs    = M.toList (cm si)
    rkvars = kvars . crhs

nonCutHyps :: SInfo a -> KIndex -> S.HashSet KVar -> [(KVar, Sol.Hyp)]
nonCutHyps si kI nKs = [ (k, nonCutHyp kI si k) | k <- S.toList nKs ]


nonCutHyp  :: KIndex -> SInfo a -> KVar -> Sol.Hyp
nonCutHyp kI si k = nonCutCube <$> cs
  where
    cs            = getSubC   si <$> M.lookupDefault [] k kI

nonCutCube :: SimpC a -> Sol.Cube
nonCutCube c = Sol.Cube (senv c) (rhsSubst c) (subcId c) (stag c)

rhsSubst :: SimpC a -> Subst
rhsSubst             = rsu . crhs
  where
    rsu (PKVar _ su) = su
    rsu _            = errorstar "Eliminate.rhsSubst called on bad input"

getSubC :: SInfo a -> Integer -> SimpC a
getSubC si i = safeLookup msg i (cm si)
  where
    msg = "getSubC: " ++ show i
