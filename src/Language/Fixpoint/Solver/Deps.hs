{-# LANGUAGE FlexibleContexts #-}
module Language.Fixpoint.Solver.Deps (
    -- * KV-Dependencies
    deps, Deps (..)
) where

import           Language.Fixpoint.Misc    (groupList)
import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Visitor (kvars, envKVars)
import qualified Data.HashMap.Strict       as M
import qualified Data.HashSet              as S
import qualified Data.Graph                as G
import           Control.Monad.State       (get, put, execState)

data Deps = Deps { depCuts    :: !(S.HashSet KVar)
                 , depNonCuts :: !(S.HashSet KVar)
                 }
            deriving (Show)

instance Monoid Deps where
  mempty                            = Deps S.empty S.empty
  mappend (Deps d1 n1) (Deps d2 n2) = Deps (S.union d1 d2) (S.union n1 n2)

dCut, dNonCut :: KVar -> Deps
dNonCut v = Deps S.empty (S.singleton v)
dCut    v = Deps (S.singleton v) S.empty

--------------------------------------------------------------------------------
-- | Compute Dependencies and Cuts ---------------------------------------------
--------------------------------------------------------------------------------

deps :: SInfo a -> Deps
deps fi   = sccsToDeps (kuts fi) sccs
  where
    subCs = M.elems (cm fi)
    edges = concatMap (subcEdges $ bs fi) subCs
    extraEdges = [(k2, KV nonSymbol) | k2 <- M.keys $ ws fi]
    -- this nonSymbol hack prevents nodes with potential outdegree 0
    -- from getting pruned by groupList (and then stronglyConnCompR)
    graph = [(k,k,ks) | (k, ks) <- groupList (edges ++ extraEdges)]
    sccs  = G.stronglyConnCompR graph

sccsToDeps :: Kuts -> [G.SCC (KVar, KVar, [KVar])] -> Deps
sccsToDeps ks xs = mconcat $ sccDep ks <$> xs

sccDep :: Kuts -> G.SCC (KVar, KVar, [KVar]) -> Deps
sccDep _ (G.AcyclicSCC (v,_,_)) = dNonCut v
sccDep ks (G.CyclicSCC vs)      = cycleDep ks vs

cycleDep _ []  = mempty
cycleDep ks vs = mconcat $ dCut v : (sccDep ks <$> sccs)
  where
    (v, vs')   = chooseCut vs ks
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

chooseCut :: [(KVar,KVar,[KVar])] -> Kuts -> (KVar, [(KVar,KVar,[KVar])])
chooseCut vs (KS ks) = (v, [x | x@(u,_,_) <- vs, u /= v])
  where
    vs' = [x | (x,_,_) <- vs]
    is  = S.intersection (S.fromList vs') ks
    v   = head $ if S.null is then vs' else S.toList is

subcEdges :: BindEnv -> SimpC a -> [(KVar, KVar)]
subcEdges be c = [(k1, k2) | k1 <- envKVars be c , k2 <- kvars $ crhs c]
