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

    , mkDoms
    ) where

import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types.Config
import qualified Language.Fixpoint.Types            as F
import           Language.Fixpoint.Types.Solutions

import qualified Data.HashMap.Strict  as M
import qualified Data.HashSet         as S
import qualified Data.Graph.Inductive as G
import qualified Data.List            as L
--------------------------------------------------------------------------------
-- | Creating an Index ---------------------------------------------------------
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


--------------------------------------------------------------------------------
mkBindExpr :: F.SInfo a -> (F.BindId |-> BindPred, KIndex |-> F.KVSub)
mkBindExpr = error "TBD:mkBindExpr"



--------------------------------------------------------------------------------
mkKvDef :: F.SInfo a -> (F.KVar |-> Hyp)
mkKvDef = error "TBD:mkKvDef"

mkKvDeps :: F.SInfo a -> S.HashSet F.KVar -> (F.KVar |-> S.HashSet F.KVar)
mkKvDeps = error "TBD:mkKvDeps"

--------------------------------------------------------------------------------
mkBindPrev :: F.SInfo a -> (F.BindId |-> F.BindId)
mkBindPrev sI
  | isTree    = M.fromList iDoms
  | otherwise = error "mkBindPrev: Malformed environments -- not tree-like!"
  where
    isTree    = length iDoms == length bindIds - 1
    iDoms     = mkDoms bindIds cEnvs
    bindIds   = fst3   <$> F.bindEnvToList (F.bs sI)
    cEnvs     = cBinds <$> M.elems         (F.cm sI)
    cBinds    = F.elemsIBindEnv . F.senv

-- >>> mkDoms [1,2,3,4,5] [[1,2,3], [1,2,4], [1,5]]
-- [(2,1),(3,2),(4,2),(5,1)]
mkDoms :: [F.BindId] -> [[F.BindId]] -> [(F.BindId, F.BindId)]
mkDoms is envs  = G.iDom g i0
  where
    i0          = minimum is
    g           :: G.Gr Int ()
    g           = G.mkGraph (node <$> is) (concatMap edges envs)
    edges       = map edge . buddies . L.sort
    node i      = (i, i)
    edge (i, j) = (i, j, ())

buddies :: [a] -> [(a, a)]
buddies (x:y:zs) = (x, y) : buddies (y:zs)
buddies _        = []

--------------------------------------------------------------------------------
-- | Encoding _all_ constraints as a single background predicate ---------------
--------------------------------------------------------------------------------
backgroundPred :: Index -> F.Pred
--------------------------------------------------------------------------------
backgroundPred = error "TBD:backgroundPred"

--------------------------------------------------------------------------------
-- | Flipping on bits for a single SubC, given current Solution ----------------
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
