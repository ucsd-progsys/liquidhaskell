module Language.Fixpoint.Solver.Deps
       ( -- * Dummy Solver for Debugging Kuts
         solve

         -- * KV-Dependencies
       , deps

         -- * Reads and Writes of Constraints
       , lhsKVars
       , rhsKVars
       ) where

import           Language.Fixpoint.Config
import           Language.Fixpoint.Misc  (groupList)
import qualified Language.Fixpoint.Types  as F

import qualified Language.Fixpoint.Visitor as V
import qualified Data.HashMap.Strict       as M
import qualified Data.Graph                as G

type KVar = F.Symbol

type Edge  = (KVar, KVar)
type Graph = [(KVar, KVar, [KVar])]
data Deps  = Deps { depCuts    :: ![KVar]
                  , depNonCuts :: ![KVar]
                  }
             deriving (Eq, Ord, Show)


--------------------------------------------------------------
-- | Dummy just for debugging --------------------------------
--------------------------------------------------------------
solve :: Config -> F.FInfo a -> IO (F.FixResult a)
--------------------------------------------------------------
solve cfg fi = do
  error "TODO: Ben fill in code that computes and prints out cuts"
  return F.Safe


--------------------------------------------------------------
-- | Compute Dependencies and Cuts ---------------------------
--------------------------------------------------------------

-- TODO: currently ignores Kuts

deps :: F.FInfo a -> Deps
deps finfo = sccsToDeps sccs
  where
    bs    = F.bs finfo
    subCs = M.elems (F.cm finfo)
    edges = concatMap (subcEdges bs) subCs
    graph = [(k,k,ks) | (k, ks) <- groupList edges]
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

subcEdges :: F.BindEnv -> F.SubC a -> [Edge]
subcEdges bs c = [(k1, k2) | k1 <- lhsKVars bs c, k2 <- rhsKVars c]

lhsKVars :: F.BindEnv -> F.SubC a -> [KVar]
lhsKVars bs c = envKVs ++ lhsKVs
  where
    envKVs    = V.envKVars bs           c
    lhsKVs    = V.reftKVars   $ F.lhsCs c

rhsKVars :: F.SubC a -> [KVar]
rhsKVars = V.reftKVars . F.rhsCs


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

---------------------------------------------------------------
