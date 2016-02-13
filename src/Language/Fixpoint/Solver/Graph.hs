{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE OverloadedStrings     #-}

module Language.Fixpoint.Solver.Graph (
       -- * Remove Constraints that don't affect Targets
         slice

       -- * Predicate describing Targets
       , isTarget

       -- * Compute Ranks / SCCs
       , graphRanks

       -- * Compute Kvar dependencies
       , cGraph, gSccs

       -- * Kvars written and read by a constraint
       , kvWriteBy, kvReadBy
       ) where


-- import           Debug.Trace (trace)
import           Prelude hiding (init)
import           Language.Fixpoint.Types.Visitor (rhsKVars, envKVars, kvars, isConcC)
import           Language.Fixpoint.Misc (errorstar, fst3, sortNub, group)
import qualified Language.Fixpoint.Types   as F
import           Language.Fixpoint.Solver.Types
import qualified Data.HashMap.Strict       as M
import qualified Data.List                 as L
import           Data.Maybe (fromMaybe)
import qualified Data.HashSet as S
import           Data.Graph (transposeG, graphFromEdges, dfs, scc, Graph, Vertex)
import           Data.Tree (flatten)

---------------------------------------------------------------------------
-- | Compute constraints that transitively affect target constraints,
--   and delete everything else from F.SInfo a
---------------------------------------------------------------------------
slice :: (F.TaggedC c a) => F.GInfo c a -> F.GInfo c a
---------------------------------------------------------------------------
slice fi = fi { F.cm = cm'
              , F.ws = ws' }
  where
     cm' = M.filterWithKey inC (F.cm fi)
     ws' = M.filterWithKey inW (F.ws fi)
     ks  = sliceKVars fi sl
     is  = S.fromList (slKVarCs sl ++ slConcCs sl)
     sl  = mkSlice fi
     inC i _ = S.member i is
     inW k _ = S.member k ks

sliceKVars :: (F.TaggedC c a) => F.GInfo c a -> Slice -> S.HashSet F.KVar
sliceKVars fi sl = S.fromList $ concatMap (subcKVars be) cs
  where
    cs           = lookupCMap cm <$> slKVarCs sl ++ slConcCs sl
    be           = F.bs fi
    cm           = F.cm fi

subcKVars :: (F.TaggedC c a) => F.BindEnv -> c a -> [F.KVar]
subcKVars be c = envKVars be c ++ rhsKVars c

---------------------------------------------------------------------------
mkSlice :: (F.TaggedC c a) => F.GInfo c a -> Slice
---------------------------------------------------------------------------
mkSlice fi        = mkSlice_ (F.cm fi) g' es v2i i2v
  where
    g'            = transposeG g  -- "inverse" of g (reverse the dep-edges)
    (g, vf, cf)   = graphFromEdges es
    es            = gEdges $ cGraph fi
    v2i           = fst3 . vf
    i2v i         = fromMaybe (errU i) $ cf i
    errU i        = errorstar $ "graphSlice: nknown constraint " ++ show i


mkSlice_ cm g' es v2i i2v = Slice { slKVarCs = kvarCs
                                  , slConcCs = concCs
                                  , slEdges  = sliceEdges kvarCs es
                                  }
  where
    -- n                  = length kvarCs
    concCs             = [ i | (i, c) <- M.toList cm, isTarget c ]
    kvarCs             = v2i <$> reachVs
    rootVs             = i2v <$> concCs
    reachVs            = concatMap flatten $ dfs g' rootVs

sliceEdges :: [CId] -> [DepEdge] -> [DepEdge]
sliceEdges is es = [ (i, i, filter inSlice js) | (i, _, js) <- es, inSlice i ]
  where
    inSlice i    = M.member i im
    im           = M.fromList $ (, ()) <$> is

-- | DO NOT DELETE!
-- sliceCSucc :: Slice -> CSucc
-- sliceCSucc sl = \i -> M.lookupDefault [] i im
  -- where
    -- im        = M.fromList [(i, is) | (i,_,is) <- slEdges sl]

---------------------------------------------------------------------------
-- | Dependencies ---------------------------------------------------------
---------------------------------------------------------------------------
kvSucc :: (F.TaggedC c a) => F.GInfo c a -> CSucc
---------------------------------------------------------------------------
kvSucc fi = succs cm rdBy
  where
    rdBy  = kvReadBy fi
    cm    = F.cm     fi

succs :: (F.TaggedC c a) => CMap (c a) -> KVRead -> CSucc
succs cm rdBy i = sortNub $ concatMap kvReads iKs
  where
    iKs         = kvWriteBy cm i
    kvReads k   = M.lookupDefault [] k rdBy

---------------------------------------------------------------------------
kvWriteBy :: (F.TaggedC c a) => CMap (c a) -> CId -> [F.KVar]
---------------------------------------------------------------------------
kvWriteBy cm = kvars . F.crhs . lookupCMap cm

---------------------------------------------------------------------------
kvReadBy :: (F.TaggedC c a) => F.GInfo c a -> KVRead
---------------------------------------------------------------------------
kvReadBy fi = group [ (k, i) | (i, ci) <- M.toList cm
                             , k       <- envKVars bs ci]
  where
    cm      = F.cm fi
    bs      = F.bs fi

---------------------------------------------------------------------------
isTarget :: (F.TaggedC c a) => c a -> Bool
---------------------------------------------------------------------------
isTarget c   = isConcC c && isNonTriv c
  where
   isNonTriv = not .  F.isTautoPred . F.crhs


---------------------------------------------------------------------------
-- | Constraint Graph -----------------------------------------------------
---------------------------------------------------------------------------
cGraph :: (F.TaggedC c a) => F.GInfo c a -> CGraph
---------------------------------------------------------------------------
cGraph fi = CGraph { gEdges = es
                   , gRanks = outRs
                   , gSucc  = next
                   , gSccs  = length sccs }
  where
    es             = [(i, i, next i) | i <- M.keys $ F.cm fi]
    next           = kvSucc fi
    (g, vf, _)     = graphFromEdges es
    (outRs, sccs)  = graphRanks g vf

---------------------------------------------------------------------------
-- | Ranks from Graph -----------------------------------------------------
---------------------------------------------------------------------------
graphRanks :: Graph -> (Vertex -> DepEdge) -> (CMap Int, [[Vertex]])
---------------------------------------------------------------------------
graphRanks g vf = (M.fromList irs, sccs)
  where
    irs        = [(v2i v, r) | (r, vs) <- rvss, v <- vs ]
    rvss       = zip [0..] sccs
    sccs       = L.reverse $ map flatten $ scc g
    v2i        = fst3 . vf
