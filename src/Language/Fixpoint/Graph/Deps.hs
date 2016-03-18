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

      -- * Eliminatable KVars
      , Elims (..)
      , elimVars
      , elimDeps

      -- * Compute Raw Dependencies
      , kvEdges

      -- * Partition
      , decompose

      -- * Debug
      , graphStatistics
      ) where

import           Prelude hiding (init)
import           Data.Maybe                       (mapMaybe, fromMaybe)
import           Data.Tree (flatten)
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Utils.Files
import           Language.Fixpoint.Types.Config
import qualified Language.Fixpoint.Types.Visitor      as V
import           Language.Fixpoint.Types.PrettyPrint
import qualified Language.Fixpoint.Types              as F
import           Language.Fixpoint.Graph.Types
import           Language.Fixpoint.Graph.Reducible  (isReducible)
import           Language.Fixpoint.Graph.Indexed

import           Control.Monad             (when)
import qualified Data.HashSet                         as S
import qualified Data.List                            as L
import qualified Data.HashMap.Strict                  as M
import qualified Data.Graph                           as G
import qualified Data.Tree                            as T
import           Data.Function (on)
import           Data.Hashable
import           Text.PrettyPrint.HughesPJ

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
decompose :: (F.TaggedC c a) => F.GInfo c a -> KVComps
-------------------------------------------------------------------------------
decompose si = map (fst3 . f) <$> vss
  where
    (g,f,_)  = G.graphFromEdges . kvgEdges . kvGraph $ si
    vss      = T.flatten <$> G.components g

-------------------------------------------------------------------------------
kvGraph :: (F.TaggedC c a) => F.GInfo c a -> KVGraph
-------------------------------------------------------------------------------
kvGraph = edgeGraph . kvEdges

edgeGraph :: [CEdge] -> KVGraph
edgeGraph es = KVGraph [(v,v,vs) | (v, vs) <- groupList es ]

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
-- | Eliminated Dependencies
--------------------------------------------------------------------------------
elimDeps :: F.SInfo a -> [CEdge] -> S.HashSet F.KVar -> CDeps
elimDeps si es nonKutVs = graphDeps si (graphElim es nonKutVs)

{- | `graphElim` "eliminates" a kvar k by replacing every "path"

          ki -> ci -> k -> c

      with an edge

          ki ------------> c

es = [ id_1 : id_1, id_2 : id_2, id_3 : id_3, id_4 : id_4, id_5 : id_5
     , "k1" : $k1*, "k0" : $k0*, $k1* : $k1*, $k0* : $k0*, id_1 : "k0"
     , id_2 : "k0", "k0" : id_3, id_3 : "k1", "k1" : id_4, id_4 : "k0"
     , "k1" : id_5]] :


     ["k0" : id_4, "k0" : id_5, "k0" : id_3, "k0" : $k0*, $k0* : $k0*
     , $k1* : $k1*, id_2 : "k0", id_2 : id_2, id_3 : id_3, id_1 : "k0"
     , id_1 : id_1, id_4 : "k0", id_4 : id_4, id_5 : id_5]

-}

graphElim :: [CEdge] -> S.HashSet F.KVar -> [CEdge]
graphElim es ks = {- tracepp msg $ -} ikvgEdges $ elimKs ks $ edgesIkvg es
  where
    -- msg         = "graphElim: ks = " ++ showpp ks ++ "\nes = " ++ showpp es
    elimKs      = flip (S.foldl' elimK)

elimK  :: IKVGraph -> F.KVar -> IKVGraph
elimK g k   = (g `addLinks` es') `delNodes` (kV : cis)
  where
   es'      = [(ki, c) | ki@(KVar _) <- kis, c@(Cstr _) <- cs]
   cs       = getSuccs g kV
   cis      = getPreds g kV
   kis      = concatMap (getPreds g) cis
   kV       = KVar k


{-
-- ORIG BLCOSMAN: graphElim :: [CEdge] -> S.HashSet F.KVar -> [CEdge]
-- ORIG BLCOSMAN: graphElim = S.foldl' graphElimSingle
-- ORIG BLCOSMAN:
-- ORIG BLCOSMAN: graphElimSingle :: [CEdge] -> F.KVar -> [CEdge]
-- ORIG BLCOSMAN: graphElimSingle cs k = filter (elimCsK cIns k) (cs ++ newEdges)
  -- ORIG BLCOSMAN: where
    -- ORIG BLCOSMAN: cOuts    = [c | (KVar k1, Cstr c) <- cs, k1 == k]
    -- ORIG BLCOSMAN: cIns     = [c | (Cstr c, KVar k1) <- cs, k1 == k]
    -- ORIG BLCOSMAN: newEdges = concatMap (newEdgesSingle cs cOuts) cIns
-- ORIG BLCOSMAN:
-- ORIG BLCOSMAN: newEdgesSingle :: [CEdge] -> [Integer] -> Integer -> [CEdge]
-- ORIG BLCOSMAN: newEdgesSingle cs cOuts cIn = [(KVar k, Cstr c) | k <- kIns, c <- cOuts]
  -- ORIG BLCOSMAN: where
    -- ORIG BLCOSMAN: kIns                    = [k | (KVar k, Cstr c) <- cs, c == cIn]
-- ORIG BLCOSMAN:
-- ORIG BLCOSMAN: elimCsK :: [Integer] -> F.KVar -> CEdge -> Bool
-- ORIG BLCOSMAN: elimCsK cIns k (v1, v2) = okV v1 && okV v2
  -- ORIG BLCOSMAN: where
    -- ORIG BLCOSMAN: okV (Cstr c)   = c `notElem` cIns
    -- ORIG BLCOSMAN: okV (KVar k1)  = k1 /= k
    -- ORIG BLCOSMAN: okV (DKVar k1) = k1 /= k
-}

--------------------------------------------------------------------------------
-- | Generic Dependencies ------------------------------------------------------
--------------------------------------------------------------------------------
data Elims a
  = Deps { depCuts    :: !(S.HashSet a)
         , depNonCuts :: !(S.HashSet a)
         }
    deriving (Show)

instance (Eq a, Hashable a) => Monoid (Elims a) where
  mempty                            = Deps S.empty S.empty
  mappend (Deps d1 n1) (Deps d2 n2) = Deps (S.union d1 d2) (S.union n1 n2)

dCut, dNonCut :: (Hashable a) => a -> Elims a
dNonCut v = Deps S.empty (S.singleton v)
dCut    v = Deps (S.singleton v) S.empty

--------------------------------------------------------------------------------
-- | Compute Dependencies and Cuts ---------------------------------------------
--------------------------------------------------------------------------------
elimVars :: (F.TaggedC c a) => Config -> F.GInfo c a -> ([CEdge], Elims F.KVar)
--------------------------------------------------------------------------------
elimVars cfg si = (es, ds)
  where
    ds          = forceKuts ks . edgeDeps . removeKutEdges ks $ es
    ks          = cutVars cfg si
    es          = kvEdges si

removeKutEdges ::  S.HashSet F.KVar -> [CEdge] -> [CEdge]
removeKutEdges ks = filter (not . isKut . snd) -- [ (u, v) | (u, v) <- es, isNotCut v ]
  where
    cutVs         = S.map KVar ks
    isKut         = (`S.member` cutVs)

cutVars :: (F.TaggedC c a) => Config -> F.GInfo c a -> S.HashSet F.KVar
cutVars _ si = F.ksVars . F.kuts $ si
  -- / | useCuts cfg = F.ksVars . F.kuts $ si
  -- / | otherwise   = S.empty

forceKuts :: (Hashable a, Eq a) => S.HashSet a -> Elims a  -> Elims a
forceKuts xs (Deps cs ns) = Deps (S.union cs xs) (S.difference ns xs)


edgeDeps :: [CEdge] -> Elims F.KVar
edgeDeps es     = Deps (takeK cs) (takeK ns)
  where
    Deps cs ns  = gElims cutF (kvgEdges $ edgeGraph es)
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
gElims :: (Cutable a) => Cutter a -> [(a, a, [a])] -> Elims a
--------------------------------------------------------------------------------
gElims f g = sccsToDeps f (G.stronglyConnCompR g)


sccsToDeps :: (Cutable a) => Cutter a -> [G.SCC (a, a, [a])] -> Elims a
sccsToDeps f xs = mconcat $ sccDep f <$> xs

sccDep :: (Cutable a) =>  Cutter a -> G.SCC (a, a, [a]) -> Elims a
sccDep _ (G.AcyclicSCC (v,_,_)) = dNonCut v
sccDep f (G.CyclicSCC vs)      = cycleDep f vs


cycleDep :: (Cutable a) => Cutter a -> [(a,a,[a])] -> Elims a
cycleDep _ [] = mempty
cycleDep f vs = addCut f (f vs)

addCut _ Nothing         = mempty
addCut f (Just (v, vs')) = mconcat $ dCut v : (sccDep f <$> sccs)
  where
    sccs                 = G.stronglyConnCompR vs'



---------------------------------------------------------------------------
graphDeps :: F.SInfo a -> [CEdge] -> CDeps
---------------------------------------------------------------------------
graphDeps fi cs = CDs { cSucc   = gSucc cg
                      , cNumScc = gSccs cg
                      , cRank   = M.fromList [(i, rf i) | i <- is ]
                      }
  where
    rf    = rankF (F.cm fi) outRs inRs
    inRs  = inRanks fi es outRs
    outRs = gRanks cg
    es    = gEdges cg
    cg    = cGraphCE cs
    is    = [i | (Cstr i, _) <- cs]

--TODO merge these with cGraph and kvSucc
cGraphCE :: [CEdge] -> CGraph
cGraphCE cs = CGraph { gEdges = es
                     , gRanks = outRs
                     , gSucc  = next
                     , gSccs  = length sccs }
  where
    es             = [(i, i, next i) | (Cstr i, _) <- cs]
    next           = kvSuccCE cs
    (g, vf, _)     = G.graphFromEdges es
    (outRs, sccs)  = graphRanks g vf

kvSuccCE :: [CEdge] -> CSucc
kvSuccCE cs i = sortNub $ concatMap kvReads iKs
  where
    rdBy      = group [(k, i) | (KVar k, Cstr i) <- cs]
    iKs       = [k | (Cstr i1, KVar k) <- cs, i == i1]
    kvReads k = M.lookupDefault [] k rdBy

rankF :: CMap (F.SimpC a) -> CMap Int -> CMap Int -> CId -> Rank
rankF cm outR inR = \i -> Rank (outScc i) (inScc i) (tag i)
  where
    outScc        = lookupCMap outR
    inScc         = lookupCMap inR
    tag           = F._ctag . lookupCMap cm

---------------------------------------------------------------------------
inRanks :: F.SInfo a -> [DepEdge] -> CMap Int -> CMap Int
---------------------------------------------------------------------------
inRanks fi es outR
  | ks == mempty      = outR
  | otherwise         = fst $ graphRanks g' vf'
  where
    ks                = F.kuts fi
    cm                = F.cm fi
    (g', vf', _)      = G.graphFromEdges es'
    es'               = [(i, i, filter (not . isCut i) js) | (i,_,js) <- es ]
    isCut i j         = S.member i cutCIds && isEqOutRank i j
    isEqOutRank i j   = lookupCMap outR i == lookupCMap outR j
    cutCIds           = S.fromList [i | i <- M.keys cm, isKutWrite i ]
    isKutWrite        = any (`F.ksMember` ks) . kvWriteBy cm




--------------------------------------------------------------------------------
graphStatistics :: Config -> F.SInfo a -> IO ()
--------------------------------------------------------------------------------
graphStatistics cfg si = when (elimStats cfg) $ do
  writeGraph f  (kvGraph si)
  appendFile f . ppc . ptable $ graphStats cfg si
  where
    f     = queryFile Dot cfg
    ppc d = showpp $ vcat [" ", " ", "/*", pprint d, "*/"]

data Stats = Stats {
    stNumKVCuts   :: !Int   -- ^ number of kvars whose removal makes deps acyclic
  , stNumKVNonLin :: !Int   -- ^ number of kvars that appear >= 2 in some LHS
  , stNumKVTotal  :: !Int   -- ^ number of kvars
  , stIsReducible :: !Bool  -- ^ is dep-graph reducible
  , stSetKVNonLin :: S.HashSet F.KVar -- ^ set of non-linear kvars
  }

instance PTable Stats where
  ptable (Stats {..})  = DocTable [
      ("# KVars [Cut]"    , pprint stNumKVCuts)
    , ("# KVars [NonLin]" , pprint stNumKVNonLin)
    , ("# KVars [All]"    , pprint stNumKVTotal)
    , ("# Reducible"      , pprint stIsReducible)
    , ("KVars NonLin"     , pprint stSetKVNonLin)
    ]

graphStats :: Config -> F.SInfo a -> Stats
graphStats cfg si = Stats {
    stNumKVCuts   = S.size (depCuts d)
  , stNumKVNonLin = S.size  nlks
  , stNumKVTotal  = S.size (depCuts d) + S.size (depNonCuts d)
  , stIsReducible = isReducible si
  , stSetKVNonLin = nlks
  }
  where
    nlks          = nlKVars si
    d             = snd $ elimVars cfg si

nlKVars :: (F.TaggedC c a) => F.GInfo c a -> S.HashSet F.KVar
nlKVars fi = S.unions $ nlKVarsC bs <$> cs
  where
    bs     = F.bs fi
    cs     = M.elems (F.cm fi)

nlKVarsC :: (F.TaggedC c a) => F.BindEnv -> c a -> S.HashSet F.KVar
nlKVarsC bs c = S.fromList [ k |  (k, n) <- V.envKVarsN bs c, n >= 2]
