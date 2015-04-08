module Language.Fixpoint.Solver.Deps where


import qualified Language.Fixpoint.Types        as F

import qualified Language.Fixpoint.Visitor as V
import qualified Data.HashMap.Strict       as M
import qualified Data.Graph                as G
import Data.Hashable (Hashable)

type KVar = F.Symbol

type Edge = (KVar,KVar)
type Graph = [(KVar,KVar,[KVar])]

data Deps = Deps { depCuts    :: ![KVar]
                 , depNonCuts :: ![KVar]
                 }
            deriving (Eq, Ord, Show)

deps :: F.FInfo a -> Deps
deps finfo = sccsToDeps sccs
  where
    subCs = M.elems (F.cm finfo)
    edges = concatMap helper subCs
    graph = makeGraph edges
    sccs  = G.stronglyConnCompR graph

sccsToDeps :: [G.SCC (KVar,KVar,[KVar])] -> Deps
sccsToDeps xs = bar xs (Deps [] [])

bar :: [G.SCC (KVar,KVar,[KVar])] -> Deps -> Deps
bar []                    deps = deps
bar (G.AcyclicSCC (v,_,_) : xs) deps = bar xs (deps { depNonCuts = v : (depNonCuts deps) })
bar (G.CyclicSCC vs       : xs) deps = bar xs deps'
  where
    deps' = baz deps vs

-- assumes its input is *STRONGLY CONNECTED* (and 2+ vtxs)
baz :: Deps -> Graph -> Deps
baz deps ((v,_,_):vs) = bar sccs' deps'
  where
    sccs' = G.stronglyConnCompR vs
    deps' = (deps { depCuts = v : (depCuts deps) })

-- TODO: currently ignores bindenvs
helper :: F.SubC a -> [(KVar,KVar)]
helper subC = [(k1,k2) | k1 <- lhsKVars , k2 <- rhsKVars]
  where
    lhsKVars = V.reftKVars $ F.lhsCs subC
    rhsKVars = V.reftKVars $ F.rhsCs subC

makeGraph :: [Edge] -> Graph
makeGraph es = [(k,k,ks) | (k,ks) <- foo M.empty es]

foo :: (Eq a, Hashable a) => M.HashMap a [a] -> [(a,a)] -> [(a,[a])]
foo m [] = M.toList m
foo m es = foo (M.insertWith (++) u [v] m) (tail es)
  where
    (u,v) = head es

{-
data FInfo a = FI { bs    :: !BindEnv
                  , kuts  :: Kuts
                  , ...}

data SubC a = SubC { senv  :: !IBindEnv
                   , ...}

data BindEnv       = BE { beSize  :: Int
                        , beBinds :: M.HashMap BindId (Symbol, SortedReft)
                        }

newtype IBindEnv   = FB (S.HashSet BindId)
-}

