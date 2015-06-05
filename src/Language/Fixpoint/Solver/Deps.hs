module Language.Fixpoint.Solver.Deps
       ( -- * Dummy Solver for Debugging Kuts
         solve

         -- * KV-Dependencies
       , deps
       , Deps (..)

         -- * Reads and Writes of Constraints
       , lhsKVars
       , rhsKVars
       ) where

import           Language.Fixpoint.Config
import           Language.Fixpoint.Misc  (groupList)
import           Language.Fixpoint.Names (nonSymbol)
import qualified Language.Fixpoint.Types  as F

import qualified Language.Fixpoint.Visitor as V
import qualified Data.HashMap.Strict       as M
import qualified Data.HashSet              as S
import qualified Data.Graph                as G

import Control.Monad.State

data Deps  = Deps { depCuts    :: ![F.KVar]
                  , depNonCuts :: ![F.KVar]
                  }
             deriving (Eq, Ord, Show)


--------------------------------------------------------------
-- | Dummy just for debugging --------------------------------
--------------------------------------------------------------
solve :: Config -> F.FInfo a -> IO (F.FixResult a)
--------------------------------------------------------------
solve _ fi = do
  let d = deps fi
  print "(begin cuts debug)"
  print "Cuts:"
  print (depCuts d)
  print "Non-cuts:"
  print (depNonCuts d)
  print "(end cuts debug)"
  return F.Safe


--------------------------------------------------------------
-- | Compute Dependencies and Cuts ---------------------------
--------------------------------------------------------------

deps :: F.FInfo a -> Deps
deps finfo = sccsToDeps sccs (F.kuts finfo)
  where
    bs    = F.bs finfo
    subCs = M.elems (F.cm finfo)
    edges = concatMap (subcEdges bs) subCs
    graph = [(k,k,ks) | (k, ks) <- groupList edges]
    sccs  = G.stronglyConnCompR graph

sccsToDeps :: [G.SCC (F.KVar, F.KVar, [F.KVar])] -> F.Kuts -> Deps
sccsToDeps xs ks = execState (mapM_ (bar ks) xs) (Deps [] [])
  where
    bar :: F.Kuts -> G.SCC (F.KVar, F.KVar,[F.KVar]) -> State Deps ()
    bar _  (G.AcyclicSCC (v,_,_)) = do ds <- get
                                       put ds {depNonCuts = v : depNonCuts ds}
    bar ks (G.CyclicSCC vs)       = do let (v,vs') = chooseCut vs ks
                                       ds <- get
                                       put ds {depCuts = v : depCuts ds}
                                       mapM_ (bar ks) (G.stronglyConnCompR vs')

chooseCut :: [(F.KVar, F.KVar, [F.KVar])] -> F.Kuts -> (F.KVar, [(F.KVar, F.KVar,[F.KVar])])
chooseCut vs (F.KS ks) = (v, [x | x@(u,_,_) <- vs, u /= v])
  where
    vs' = [x | (x,_,_) <- vs]
    is  = S.intersection (S.fromList vs') ks
    v   = head $ if S.null is then vs' else S.toList is

subcEdges :: F.BindEnv -> F.SubC a -> [(F.KVar, F.KVar)]
subcEdges bs c = [(k1, k2)        | k1 <- lhsKVars bs c
                                  , k2 <- rhsKVars c    ]
              ++ [(k2, F.KV nonSymbol) | k2 <- rhsKVars c]
-- this nonSymbol hack is one way to prevent nodes with potential
-- outdegree 0 from getting pruned by stronglyConnCompR

lhsKVars :: F.BindEnv -> F.SubC a -> [F.KVar]
lhsKVars bs c = envKVs ++ lhsKVs
  where
    envKVs    = V.envKVars bs           c
    lhsKVs    = V.kvars       $ F.lhsCs c

rhsKVars :: F.SubC a -> [F.KVar]
rhsKVars = V.kvars . F.rhsCs


---------------------------------------------------------------
