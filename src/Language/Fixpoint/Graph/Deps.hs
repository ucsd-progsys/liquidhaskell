{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE RecordWildCards       #-}

module Language.Fixpoint.Graph.Deps (
       -- * Remove Constraints that don't affect Targets
         slice

       -- * Predicate describing Targets
       , isTarget

       -- * Compute Ranks / SCCs
       , graphRanks

       -- * Compute Kvar dependencies
       , cGraph, gSccs

       -- * Kvars written and read by a constraint
       , kvWriteBy
       -- , kvReadBy

      -- * Queries over dependencies
      , GDeps (..)
      , deps
      , kvGraph
      , decompose

       ) where

import           Prelude hiding (init)
import           Data.Maybe                       (mapMaybe, fromMaybe)
import           Data.Tree (flatten)
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types.Config
import qualified Language.Fixpoint.Types.Visitor      as V
import qualified Language.Fixpoint.Types              as F
import           Language.Fixpoint.Graph.Types

import qualified Data.HashSet                         as S
import qualified Data.List                            as L
import qualified Data.HashMap.Strict                  as M
import qualified Data.Graph                           as G
import qualified Data.Tree                            as T
import           Data.Function (on)
import           Data.Hashable

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
subcKVars be c = V.envKVars be c ++ V.rhsKVars c

---------------------------------------------------------------------------
mkSlice :: (F.TaggedC c a) => F.GInfo c a -> Slice
---------------------------------------------------------------------------
mkSlice fi        = mkSlice_ (F.cm fi) g' es v2i i2v
  where
    g'            = G.transposeG g  -- "inverse" of g (reverse the dep-edges)
    (g, vf, cf)   = G.graphFromEdges es
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
    reachVs            = concatMap flatten $ G.dfs g' rootVs

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
isTarget :: (F.TaggedC c a) => c a -> Bool
---------------------------------------------------------------------------
isTarget c   = V.isConcC c && isNonTriv c
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
    (g, vf, _)     = G.graphFromEdges es
    (outRs, sccs)  = graphRanks g vf

---------------------------------------------------------------------------
-- | Ranks from Graph -----------------------------------------------------
---------------------------------------------------------------------------
graphRanks :: G.Graph -> (G.Vertex -> DepEdge) -> (CMap Int, [[G.Vertex]])
---------------------------------------------------------------------------
graphRanks g vf = (M.fromList irs, sccs)
  where
    irs        = [(v2i v, r) | (r, vs) <- rvss, v <- vs ]
    rvss       = zip [0..] sccs
    sccs       = L.reverse $ map flatten $ G.scc g
    v2i        = fst3 . vf


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
kvWriteBy cm = V.kvars . F.crhs . lookupCMap cm

---------------------------------------------------------------------------
kvReadBy :: (F.TaggedC c a) => F.GInfo c a -> KVRead
---------------------------------------------------------------------------
kvReadBy fi = group [ (k, i) | (i, ci) <- M.toList cm
                             , k       <- V.envKVars bs ci]
  where
    cm      = F.cm fi
    bs      = F.bs fi



-------------------------------------------------------------------------------
decompose :: KVGraph -> KVComps
-------------------------------------------------------------------------------
decompose kg = map (fst3 . f) <$> vss
  where
    (g,f,_)  = G.graphFromEdges kg
    vss      = T.flatten <$> G.components g

-------------------------------------------------------------------------------
kvGraph :: (F.TaggedC c a) => F.GInfo c a -> KVGraph
-------------------------------------------------------------------------------
kvGraph = edgeGraph . kvEdges

edgeGraph :: [CEdge] -> KVGraph
edgeGraph es = [(v,v,vs) | (v, vs) <- groupList es ]

kvEdges :: (F.TaggedC c a) => F.GInfo c a -> [CEdge]
kvEdges fi = selfes ++ concatMap (subcEdges bs) cs
  where
    bs     = F.bs fi
    cs     = M.elems (F.cm fi)
    ks     = fiKVars fi
    selfes =  [(Cstr i, Cstr i)   | c <- cs, let i = F.subcId c]
           ++ [(KVar k, DKVar k)  | k <- ks]
           ++ [(DKVar k, DKVar k) | k <- ks]


fiKVars :: F.GInfo c a -> [F.KVar]
fiKVars = M.keys . F.ws

subcEdges :: (F.TaggedC c a) => F.BindEnv -> c a -> [CEdge]
subcEdges bs c =  [(KVar k, Cstr i ) | k  <- V.envKVars bs c]
               ++ [(Cstr i, KVar k') | k' <- V.rhsKVars c ]
  where
    i          = F.subcId c

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
-- | Compute Dependencies and Cuts ---------------------------------------------
--------------------------------------------------------------------------------
deps :: (F.TaggedC c a) => Config -> F.GInfo c a -> GDeps F.KVar
--------------------------------------------------------------------------------
deps cfg si = forceCuts cutKs $ edgeDeps cutEs
  where
    cutEs   = [ (u, v) | (u, v) <- allEs, not (S.member v cutVs)]
    cutKs   = cutVars cfg si
    cutVs   = S.map KVar cutKs
    allEs   = kvEdges si

cutVars :: (F.TaggedC c a) => Config -> F.GInfo c a -> S.HashSet F.KVar
cutVars _ si = F.ksVars . F.kuts $ si
  -- / | useCuts cfg = F.ksVars . F.kuts $ si
  -- / | otherwise   = S.empty

forceCuts :: (Hashable a, Eq a) => S.HashSet a -> GDeps a  -> GDeps a
forceCuts xs (Deps cs ns) = Deps (S.union cs xs) (S.difference ns xs)


edgeDeps :: [CEdge] -> GDeps F.KVar
edgeDeps es     = Deps (takeK cs) (takeK ns)
  where
    Deps cs ns  = gDeps cutF (edgeGraph es)
    cutF        = edgeRankCut (edgeRank es)
    takeK       = sMapMaybe tx
    tx (KVar z) = Just z
    tx _        = Nothing

-- ORIG cuts :: (F.TaggedC c a) => F.GInfo c a -> S.HashSet CVertex
-- ORIG cuts = S.map KVar . F.ksVars . F.kuts

sMapMaybe :: (Hashable b, Eq b) => (a -> Maybe b) -> S.HashSet a -> S.HashSet b
sMapMaybe f = S.fromList . mapMaybe f . S.toList

--------------------------------------------------------------------------------
type EdgeRank = M.HashMap F.KVar Integer
--------------------------------------------------------------------------------
edgeRank :: [CEdge] -> EdgeRank
edgeRank es = minimum . (n :) <$> kiM
  where
    n       = 1 + maximum [ i | (Cstr i, _)     <- es ]
    kiM     = group [ (k, i) | (KVar k, Cstr i) <- es ]

edgeRankCut :: EdgeRank -> Cutter CVertex
edgeRankCut km vs = case ks of
                      [] -> Nothing
                      k:_ -> Just (KVar k, [x | x@(u,_,_) <- vs, u /= KVar k])
  where
    ks            = orderBy [k | (KVar k, _ ,_) <- vs]
    rank          = (km M.!)
    orderBy       = L.sortBy (compare `on` rank)

--------------------------------------------------------------------------------
type Cutter a = [(a, a, [a])] -> Maybe (a, [(a, a, [a])])
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
type Cutable a = (Eq a, Ord a, Hashable a, Show a)
--------------------------------------------------------------------------------
gDeps :: (Cutable a) => Cutter a -> [(a, a, [a])] -> GDeps a
--------------------------------------------------------------------------------
gDeps f g = sccsToDeps f (G.stronglyConnCompR g)


sccsToDeps :: (Cutable a) => Cutter a -> [G.SCC (a, a, [a])] -> GDeps a
sccsToDeps f xs = mconcat $ sccDep f <$> xs

sccDep :: (Cutable a) =>  Cutter a -> G.SCC (a, a, [a]) -> GDeps a
sccDep _ (G.AcyclicSCC (v,_,_)) = dNonCut v
sccDep f (G.CyclicSCC vs)      = cycleDep f vs


cycleDep :: (Cutable a) => Cutter a -> [(a,a,[a])] -> GDeps a
cycleDep _ [] = mempty
cycleDep f vs = addCut f (f vs)

addCut _ Nothing         = mempty
addCut f (Just (v, vs')) = mconcat $ dCut v : (sccDep f <$> sccs)
  where
    sccs                 = G.stronglyConnCompR vs'
