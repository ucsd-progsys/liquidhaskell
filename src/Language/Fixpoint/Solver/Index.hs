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
import           Language.Fixpoint.Graph            (CDeps (..))

import qualified Data.HashMap.Strict  as M
-- import qualified Data.HashSet         as S
import qualified Data.Graph.Inductive as G
import qualified Data.List            as L

--------------------------------------------------------------------------------
-- | Creating an Index ---------------------------------------------------------
--------------------------------------------------------------------------------
create :: Config -> F.SInfo a -> [(F.KVar, Hyp)] -> CDeps -> Index
--------------------------------------------------------------------------------
create _cfg sI kHyps cDs = FastIdx
  { bindExpr = bE
  , kvUse    = kU
  , bindPrev = mkBindPrev sI
  , kvDef    = M.fromList kHyps
  , kvDeps   = cPrev cDs
  }
  where
    (bE, kU) = mkBindExpr sI


--------------------------------------------------------------------------------
mkBindExpr :: F.SInfo a -> (F.BindId |-> BindPred, KIndex |-> F.KVSub)
mkBindExpr sI = (M.fromList ips, M.fromList kSus)
  where
    kSus = [ (k, kSu)                | (_, _, iks) <- ipks, (k, kSu) <- iks    ]
    ips  = [ (i, BP p (fst <$> iks)) | (i, p, iks) <- ipks                     ]
    ipks = [ (i, p, iks)             | (i, x, r)   <- F.bindEnvToList (F.bs sI)
                                     , let (p, iks) = mkBindPred i x r         ]

mkBindPred :: F.BindId -> F.Symbol -> F.SortedReft -> (F.Pred, [(KIndex, F.KVSub)])
mkBindPred i x sr = (F.pAnd ps, zipWith tx [0..] ks)
  where
    (ps, ks)      = F.sortedReftConcKVars x sr
    tx j k@(kv,_) = (KIndex (Bind i) j kv, k)

--------------------------------------------------------------------------------
mkBindPrev :: F.SInfo a -> (F.BindId |-> F.BindId)
mkBindPrev sI = M.fromList iDoms
  where
    -- isTree    = length iDoms == length bindIds - 1
    iDoms     = mkDoms bindIds cEnvs
    bindIds   = fst3   <$> F.bindEnvToList (F.bs sI)
    cEnvs     = cBinds <$> M.elems         (F.cm sI)
    cBinds    = F.elemsIBindEnv . F.senv

-- >>> mkDoms [1,2,3,4,5] [[1,2,3], [1,2,4], [1,5]]
-- [(2,1),(3,2),(4,2),(5,1)]
mkDoms :: ListNE F.BindId -> [[F.BindId]] -> [(F.BindId, F.BindId)]
mkDoms is envs  = G.iDom (mkEnvTree is envs) (minimum is)

mkEnvTree :: [F.BindId] -> [[F.BindId]] -> G.Gr Int ()
mkEnvTree is envs
  | isTree es   = G.mkGraph (node <$> is) es
  | otherwise   = error "mkBindPrev: Malformed environments -- not tree-like! (TODO: move into Validate)"
  where
    es          = concatMap envEdges envs
    envEdges    = map edge . buddies . L.sort
    node i      = (i, i)
    edge (i, j) = (i, j, ())

-- TODO: push the `isTree` check into Validate
isTree :: [(Int, Int, a)] -> Bool
isTree es    = allMap (sizeLE 1) inEs
  where
    inEs     = group [ (j, i) | (i, j, _) <- es]
    sizeLE n = (<= n) . length . sortNub

buddies :: [a] -> [(a, a)]
buddies (x:y:zs) = (x, y) : buddies (y:zs)
buddies _        = []

--------------------------------------------------------------------------------
-- | Encoding _all_ constraints as a single background predicate ---------------
--------------------------------------------------------------------------------
backgroundPred :: Index -> F.Pred
--------------------------------------------------------------------------------
backgroundPred = error "TBD:backgroundPred"
-- TODO: backgroundPred, lhsPred, hook into the ACTUAL SOLVER


--------------------------------------------------------------------------------
-- | Flipping on bits for a single SubC, given current Solution ----------------
--------------------------------------------------------------------------------
lhsPred :: Index -> F.SolEnv -> Solution -> F.SimpC a -> F.Expr
--------------------------------------------------------------------------------
lhsPred = error "TBD:lhsPred"


{- | [NOTE: Bit-Indexed Representation]

     The whole constraint system will be represented by a collection
     of bit indexed propositions:

      b(i) <=> pred(i)

      where pred(i) encodes the logical refinement corresponding to i-th binder.
 -}
