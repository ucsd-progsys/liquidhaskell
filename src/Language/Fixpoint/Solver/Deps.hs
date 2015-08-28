{-# LANGUAGE FlexibleContexts #-}
module Language.Fixpoint.Solver.Deps (
    -- * KV-Dependencies
    deps, Deps (..)
) where

import           Language.Fixpoint.Misc    (groupList)
import           Language.Fixpoint.Types
import           Language.Fixpoint.Visitor (lhsKVars, rhsKVars)
import           Data.HashMap.Strict       (elems)
import qualified Data.HashSet              as S
import qualified Data.Graph                as G
import           Control.Monad.State       (get, put, execState)

data Deps  = Deps { depCuts    :: ![KVar]
                  , depNonCuts :: ![KVar]
                  }
             deriving (Eq, Ord, Show)

--------------------------------------------------------------
-- | Compute Dependencies and Cuts ---------------------------
--------------------------------------------------------------

deps :: FInfo a -> Deps
deps fi = sccsToDeps sccs (kuts fi)
  where
    subCs = elems (cm fi)
    edges = concatMap (subcEdges $ bs fi) subCs
    graph = [(k,k,ks) | (k, ks) <- groupList edges]
    sccs  = G.stronglyConnCompR graph

sccsToDeps :: [G.SCC (KVar,KVar,[KVar])] -> Kuts -> Deps
sccsToDeps xs ks = execState (mapM_ go xs) (Deps [] [])
  where
    go (G.AcyclicSCC (v,_,_)) = do ds <- get
                                   put ds {depNonCuts = v : depNonCuts ds}
    go (G.CyclicSCC vs)       = do let (v,vs') = chooseCut vs ks
                                   ds <- get
                                   put ds {depCuts = v : depCuts ds}
                                   mapM_ go (G.stronglyConnCompR vs')

chooseCut :: [(KVar,KVar,[KVar])] -> Kuts -> (KVar, [(KVar,KVar,[KVar])])
chooseCut vs (KS ks) = (v, [x | x@(u,_,_) <- vs, u /= v])
  where
    vs' = [x | (x,_,_) <- vs]
    is  = S.intersection (S.fromList vs') ks
    v   = head $ if S.null is then vs' else S.toList is

subcEdges :: BindEnv -> SubC a -> [(KVar, KVar)]
subcEdges bs c = [(k1, k2)        | k1 <- lhsKVars bs c
                                  , k2 <- rhsKVars c    ]
              ++ [(k2, KV nonSymbol) | k2 <- rhsKVars c]
-- this nonSymbol hack is one way to prevent nodes with potential
-- outdegree 0 from getting pruned by stronglyConnCompR

---------------------------------------------------------------
