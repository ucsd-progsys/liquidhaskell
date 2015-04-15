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
import           Language.Fixpoint.Names (nonSymbol)
import qualified Language.Fixpoint.Types  as F

import qualified Language.Fixpoint.Visitor as V
import qualified Data.HashMap.Strict       as M
import qualified Data.HashSet              as S
import qualified Data.Graph                as G

import Control.Monad.State

type KVar = F.Symbol

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

sccsToDeps :: [G.SCC (KVar,KVar,[KVar])] -> F.Kuts -> Deps
sccsToDeps xs ks = execState (mapM_ (bar ks) xs) (Deps [] [])

bar :: F.Kuts -> G.SCC (KVar,KVar,[KVar]) -> State Deps ()
bar _  (G.AcyclicSCC (v,_,_)) = do ds <- get
                                   put ds {depNonCuts = v : depNonCuts ds}
bar ks (G.CyclicSCC vs)       = do let (v,vs') = chooseCut vs ks
                                   ds <- get
                                   put ds {depCuts = v : depCuts ds}
                                   mapM_ (bar ks) (G.stronglyConnCompR vs')

chooseCut :: [(KVar,KVar,[KVar])] -> F.Kuts -> (KVar, [(KVar,KVar,[KVar])])
chooseCut vs (F.KS ks) = (v, [x | x@(u,_,_) <- vs, u /= v])
  where
    vs' = [x | (x,_,_) <- vs]
    is  = S.intersection (S.fromList vs') ks
    v   = if (S.null is) then (head vs') 
                         else (head $ S.toList is)

subcEdges :: F.BindEnv -> F.SubC a -> [(KVar, KVar)]
subcEdges bs c = [(k1, k2)        | k1 <- lhsKVars bs c
                                  , k2 <- rhsKVars c    ]
              ++ [(k2, nonSymbol) | k2 <- rhsKVars c]
-- this nonSymbol hack is one way to prevent nodes with
-- potential outdegree 0 from getting pruned by
-- stronglyConnCompR

lhsKVars :: F.BindEnv -> F.SubC a -> [KVar]
lhsKVars bs c = envKVs ++ lhsKVs
  where
    envKVs    = V.envKVars bs           c
    lhsKVs    = V.reftKVars   $ F.lhsCs c

rhsKVars :: F.SubC a -> [KVar]
rhsKVars = V.reftKVars . F.rhsCs


---------------------------------------------------------------
