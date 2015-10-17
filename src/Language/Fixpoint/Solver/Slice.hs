{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections         #-}

module Language.Fixpoint.Solver.Slice (
       -- * Remove Constraints that don't affect Targets
         slice

       -- * Predicate describing Targets
       , isTarget

       -- * Compute Kvar dependencies
       , kvSucc

       -- * Kvars written and read by a constraint
       , kvWriteBy, kvReadBy
       ) where

import           Debug.Trace (trace)
import           Prelude hiding (init)
import           Language.Fixpoint.Visitor (envKVars, kvars, isConcC)
import           Language.Fixpoint.Misc (errorstar, fst3, sortNub, group)
import qualified Language.Fixpoint.Types   as F
import           Language.Fixpoint.Solver.Types
import qualified Data.HashMap.Strict       as M
import           Data.Maybe (fromMaybe)
import           Data.Graph (transposeG, graphFromEdges, dfs, Graph, Vertex)
import           Data.Tree (flatten)

-- import           Language.Fixpoint.PrettyPrint (PPrint (..))
-- import           Control.Arrow             (first)
-- import           Data.HashMap.Strict       ((!))
-- import qualified Data.Set                  as S
-- import qualified Data.List                 as L
-- import           Text.PrettyPrint.HughesPJ (text)

---------------------------------------------------------------------------
-- | Compute constraints that transitively affect target constraints,
--   and delete everything else from F.SInfo a
---------------------------------------------------------------------------
slice :: F.SInfo a -> F.SInfo a
---------------------------------------------------------------------------
slice fi = prune fi (mkSlice fi)

prune :: F.SInfo a -> Slice -> F.SInfo a
prune = error "FIXME"

---------------------------------------------------------------------------
mkSlice :: F.SInfo a -> Slice
---------------------------------------------------------------------------
mkSlice fi        = mkSlice_ cm g' es v2i i2v
  where
    es            = [(i, i, next i) | i <- M.keys cm]
    next          = kvSucc fi
    cm            = F.cm   fi
    (g, vf, cf)   = graphFromEdges es
    v2i           = fst3 . vf
    i2v i         = fromMaybe (errU i) $ cf i
    errU i        = errorstar $ "graphSlice: nknown constraint " ++ show i
    g'            = transposeG g  -- g'  : "inverse" of g (reverse the dep-edges)


mkSlice_ :: CMap (F.SimpC a) -> Graph -> [DepEdge] -> (Vertex -> CId) -> (CId -> Vertex) -> Slice
mkSlice_ cm g' es v2i i2v = Slice { slKVarCs = {- trace ("SLICE=" ++ show n) -} kvarCs
                                  , slConcCs = concCs
                                  , slEdges  = sliceEdges kvarCs es
                                  }
  where
    n                  = length kvarCs
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
kvSucc :: F.SInfo a -> CSucc
---------------------------------------------------------------------------
kvSucc fi = succs cm rdBy
  where
    rdBy  = kvReadBy fi
    cm    = F.cm     fi

succs :: CMap (F.SimpC a) -> KVRead -> CSucc
succs cm rdBy i = sortNub $ concatMap kvReads iKs
  where
    iKs         = kvWriteBy cm i
    kvReads k   = M.lookupDefault [] k rdBy

---------------------------------------------------------------------------
kvWriteBy :: CMap (F.SimpC a) -> CId -> [F.KVar]
---------------------------------------------------------------------------
kvWriteBy cm = kvars . F.crhs . lookupCMap cm

---------------------------------------------------------------------------
kvReadBy :: F.SInfo a -> KVRead
---------------------------------------------------------------------------
kvReadBy fi = group [ (k, i) | (i, ci) <- M.toList cm
                             , k       <- envKVars bs ci]
  where
    cm      = F.cm fi
    bs      = F.bs fi

---------------------------------------------------------------------------
isTarget :: F.SimpC a -> Bool
---------------------------------------------------------------------------
isTarget c = isConcC c && isNonTriv c
isNonTriv  = not .  F.isTautoPred . F.crhs
