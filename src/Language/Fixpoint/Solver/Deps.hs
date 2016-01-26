{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}

module Language.Fixpoint.Solver.Deps (
    -- * KV-Dependencies
    deps
  , Deps
  
    -- * Generic Dependencies
  , gDeps
  , GDeps (..)
) where

import           Data.Hashable
import           Language.Fixpoint.Misc    (groupList)
import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Visitor (kvars, envKVars)
import qualified Data.HashMap.Strict       as M
import qualified Data.HashSet              as S
import qualified Data.Graph                as G
-- import           Control.Monad.State       (get, put, execState)

type Deps = GDeps KVar
--------------------------------------------------------------------------------
-- | Compute Dependencies and Cuts ---------------------------------------------
--------------------------------------------------------------------------------
deps :: SInfo a -> Deps
--------------------------------------------------------------------------------
deps si = gDeps (cuts si) (graph si)

cuts :: SInfo a -> S.HashSet KVtx
cuts = ksVars . kuts

graph :: SInfo a -> KGrp
graph si  = [(k,k,ks) | (k, ks) <- groupList (edges ++ extraEdges)]
  where
    subCs = M.elems (cm si)
    edges = concatMap (subcEdges $ bs si) subCs
    extraEdges = [(k2, KV nonSymbol) | k2 <- M.keys $ ws si]
    -- ^ this nonSymbol hack prevents nodes with potential outdegree 0
    -- from getting pruned by groupList (and then stronglyConnCompR)

subcEdges :: BindEnv -> SimpC a -> [(KVtx, KVtx)]
subcEdges be c = [(k1, k2) | k1 <- envKVars be c , k2 <- kvars $ crhs c]

type KVtx = KVar
type KGrp = [(KVtx, KVtx, [KVtx])]

{-
a       := (Rank, KV)
Rank(K) := MIN_i k in LHS c_i
-}

--------------------------------------------------------------------------------
-- | Generic Dependencies ------------------------------------------------------
--------------------------------------------------------------------------------
data GDeps a
  = Deps { depCuts    :: !(S.HashSet a)
         , depNonCuts :: !(S.HashSet a)
         }
    deriving (Show)

instance (Eq a, Hashable a) => Monoid (GDeps a) where
  mempty                            = Deps S.empty S.empty
  mappend (Deps d1 n1) (Deps d2 n2) = Deps (S.union d1 d2) (S.union n1 n2)

dCut, dNonCut :: (Hashable a) => a -> GDeps a
dNonCut v = Deps S.empty (S.singleton v)
dCut    v = Deps (S.singleton v) S.empty

--------------------------------------------------------------------------------
gDeps :: (Eq a, Ord a, Hashable a) => S.HashSet a -> [(a,a,[a])] -> GDeps a
--------------------------------------------------------------------------------
gDeps ks g = sccsToDeps ks (G.stronglyConnCompR g)

sccsToDeps :: (Ord a, Eq a, Hashable a) => S.HashSet a -> [G.SCC (a, a, [a])] -> GDeps a
sccsToDeps ks xs = mconcat $ sccDep ks <$> xs

sccDep :: (Ord a, Hashable a, Eq a) =>  S.HashSet a -> G.SCC (a, a, [a]) -> GDeps a
sccDep _ (G.AcyclicSCC (v,_,_)) = dNonCut v
sccDep ks (G.CyclicSCC vs)      = cycleDep ks vs

cycleDep :: (Ord a, Hashable a) => S.HashSet a -> [(a,a,[a])] -> GDeps a
cycleDep _ []  = mempty
cycleDep ks vs = mconcat $ dCut v : (sccDep ks <$> sccs)
  where
    (v, vs')   = chooseCut ks vs
    sccs       = G.stronglyConnCompR vs'

{-
sccsToDeps :: [G.SCC (KVar, KVar, [KVar])] -> Kuts -> Deps
sccsToDeps xs ks = execState (mapM_ go xs) (Deps S.empty S.empty)
  where
    go (G.AcyclicSCC (v,_,_)) = do ds <- get
                                   put ds {depNonCuts = S.insert v $ depNonCuts ds}
    go (G.CyclicSCC vs)       = do let (v, vs') = chooseCut vs ks
                                   ds <- get
                                   put ds {depCuts = S.insert v $ depCuts ds}
                                   mapM_ go (G.stronglyConnCompR vs')
-}

chooseCut :: (Eq a, Hashable a) => S.HashSet a -> [(a, a, [a])] -> (a, [(a, a, [a])])
chooseCut ks vs = (v, [x | x@(u,_,_) <- vs, u /= v])
  where
    vs' = [x | (x,_,_) <- vs]
    is  = S.intersection (S.fromList vs') ks
    v   = head $ if S.null is then vs' else S.toList is
       -- ^ -- we select a RANDOM element,
       ------- instead pick the "first" element.
