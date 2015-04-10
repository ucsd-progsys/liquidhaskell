module Language.Fixpoint.Solver.Deps where


import qualified Language.Fixpoint.Types        as F

import qualified Language.Fixpoint.Visitor as V
import qualified Data.HashMap.Strict       as M
import qualified Data.Graph                as G

type KVar = F.Symbol

type Edge = (KVar,KVar)
type Graph = [(KVar,KVar,[KVar])]

data Deps = Deps { depCuts    :: ![KVar]
                 , depNonCuts :: ![KVar]
                 }
            deriving (Eq, Ord, Show)

-- TODO: currently ignores Kuts

deps :: F.FInfo a -> Deps
deps finfo = sccsToDeps sccs
  where
    bs    = F.bs finfo
    subCs = M.elems (F.cm finfo)
    edges = concatMap (depsHelper bs) subCs
    graph = makeGraph edges
    sccs  = G.stronglyConnCompR graph

sccsToDeps :: [G.SCC (KVar,KVar,[KVar])] -> Deps
sccsToDeps xs = bar xs (Deps [] [])

-- TODO: rewrite using State monad :)
bar :: [G.SCC (KVar,KVar,[KVar])] -> Deps -> Deps
bar []                              deps = deps
bar (G.AcyclicSCC (v,_,_)     : xs) deps = bar xs (deps { depNonCuts = v : (depNonCuts deps) })
bar (G.CyclicSCC ((v,_,_):vs) : xs) deps = bar xs (bar sccs' deps')
  where
    sccs' = G.stronglyConnCompR vs
    deps' = (deps { depCuts = v : (depCuts deps) })

-- TODO: currently ignores bindenvs
depsHelper :: F.BindEnv -> F.SubC a -> [Edge]
depsHelper bs subC = [(k1,k2) | k1 <- lhsKVars' , k2 <- rhsKVars]
  where
    lhsKVars'      = envKVars ++ lhsKVars
    envKVars       = V.envKVars bs           subC
    lhsKVars       = V.reftKVars   $ F.lhsCs subC
    rhsKVars       = V.reftKVars   $ F.rhsCs subC

makeGraph :: [Edge] -> Graph
makeGraph es = [(k,k,ks) | (k,ks) <- go M.empty es]
  where
    go m []         = M.toList m
    go m ((u,v):es) = go (M.insertWith (++) u [v] m) es

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
