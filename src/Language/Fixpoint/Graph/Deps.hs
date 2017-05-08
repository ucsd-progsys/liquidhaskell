{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeOperators         #-}
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
import           Data.Function (on)
import           Data.Hashable
import           Text.PrettyPrint.HughesPJ
import           Debug.Trace (trace)

--------------------------------------------------------------------------------
-- | Compute constraints that transitively affect target constraints,
--   and delete everything else from F.SInfo a
--------------------------------------------------------------------------------
slice :: (F.TaggedC c a) => Config -> F.GInfo c a -> F.GInfo c a
--------------------------------------------------------------------------------
slice cfg fi 
  | noslice cfg 
  = fi 
  | otherwise
  = fi { F.cm = cm'
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

--------------------------------------------------------------------------------
mkSlice :: (F.TaggedC c a) => F.GInfo c a -> Slice
--------------------------------------------------------------------------------
mkSlice fi        = mkSlice_ (F.cm fi) g' es v2i i2v
  where
    g'            = G.transposeG g  -- "inverse" of g (reverse the dep-edges)
    (g, vf, cf)   = G.graphFromEdges es
    es            = gEdges $ cGraph fi
    v2i           = fst3 . vf
    i2v i         = fromMaybe (errU i) $ cf i
    errU i        = errorstar $ "graphSlice: Unknown constraint " ++ show i

mkSlice_ :: F.TaggedC c a
         => M.HashMap F.SubcId (c a)
         -> G.Graph
         -> [DepEdge]
         -> (G.Vertex -> F.SubcId)
         -> (F.SubcId -> G.Vertex)
         -> Slice
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

sliceEdges :: [F.SubcId] -> [DepEdge] -> [DepEdge]
sliceEdges is es = [ (i, i, filter inSlice js) | (i, _, js) <- es, inSlice i ]
  where
    inSlice i    = M.member i im
    im           = M.fromList $ (, ()) <$> is

-- | DO NOT DELETE!
-- sliceCSucc :: Slice -> CSucc
-- sliceCSucc sl = \i -> M.lookupDefault [] i im
  -- where
    -- im        = M.fromList [(i, is) | (i,_,is) <- slEdges sl]

--------------------------------------------------------------------------------
isTarget :: (F.TaggedC c a) => c a -> Bool
--------------------------------------------------------------------------------
isTarget c   = V.isConcC c && isNonTriv c
  where
   isNonTriv = not .  F.isTautoPred . F.crhs


--------------------------------------------------------------------------------
-- | Constraint Graph ----------------------------------------------------------
--------------------------------------------------------------------------------
cGraph :: (F.TaggedC c a) => F.GInfo c a -> CGraph
---------------------------------------------------------------------------
cGraph fi = CGraph { gEdges = es
                   , gRanks = outRs
                   , gSucc  = next
                   , gSccs  = length sccs }
  where
    es             = [(i, i, M.lookupDefault [] i next) | i <- M.keys $ F.cm fi]
    next           = kvSucc fi
    (g, vf, _)     = G.graphFromEdges es
    (outRs, sccs)  = graphRanks g vf

--------------------------------------------------------------------------------
-- | Ranks from Graph ----------------------------------------------------------
--------------------------------------------------------------------------------
graphRanks :: G.Graph -> (G.Vertex -> DepEdge) -> (CMap Int, [[G.Vertex]])
---------------------------------------------------------------------------
graphRanks g vf = (M.fromList irs, sccs)
  where
    irs        = [(v2i v, r) | (r, vs) <- rvss, v <- vs ]
    rvss       = zip [0..] sccs
    sccs       = L.reverse $ map flatten $ G.scc g
    v2i        = fst3 . vf

--------------------------------------------------------------------------------
-- | Dependencies --------------------------------------------------------------
--------------------------------------------------------------------------------
kvSucc :: (F.TaggedC c a) => F.GInfo c a -> CMap [F.SubcId]
--------------------------------------------------------------------------------
kvSucc fi = succs cm rdBy
  where
    rdBy  = kvReadBy fi
    cm    = F.cm     fi

succs :: (F.TaggedC c a) => CMap (c a) -> KVRead -> CMap [F.SubcId]
succs cm rdBy = (sortNub . concatMap kvReads . kvWrites) <$> cm
  where
    kvReads k = M.lookupDefault [] k rdBy
    kvWrites  = V.kvars . F.crhs

--------------------------------------------------------------------------------
kvWriteBy :: (F.TaggedC c a) => CMap (c a) -> F.SubcId -> [F.KVar]
--------------------------------------------------------------------------------
kvWriteBy cm = V.kvars . F.crhs . lookupCMap cm

--------------------------------------------------------------------------------
kvReadBy :: (F.TaggedC c a) => F.GInfo c a -> KVRead
--------------------------------------------------------------------------------
kvReadBy fi = group [ (k, i) | (i, ci) <- M.toList cm
                             , k       <- V.envKVars bs ci]
  where
    cm      = F.cm fi
    bs      = F.bs fi

--------------------------------------------------------------------------------
decompose :: (F.TaggedC c a) => F.GInfo c a -> KVComps
--------------------------------------------------------------------------------
decompose = componentsWith (kvgEdges . kvGraph)

--------------------------------------------------------------------------------
kvGraph :: (F.TaggedC c a) => F.GInfo c a -> KVGraph
--------------------------------------------------------------------------------
kvGraph = edgeGraph . kvEdges

edgeGraph :: [CEdge] -> KVGraph
edgeGraph es = KVGraph [(v, v, vs) | (v, vs) <- groupList es ]

kvEdges :: (F.TaggedC c a) => F.GInfo c a -> [CEdge]
kvEdges fi = selfes ++ concatMap (subcEdges bs) cs
  where
    bs     = F.bs fi
    cs     = M.elems (F.cm fi)
    ks     = fiKVars fi
    selfes =  [(Cstr i , Cstr  i) | c <- cs, let i = F.subcId c]
           ++ [(KVar k , DKVar k) | k <- ks]
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
elimDeps :: (F.TaggedC c a) => F.GInfo c a -> [CEdge] -> S.HashSet F.KVar -> CDeps
elimDeps si es nonKutVs = graphDeps si es'
  where
    es'                 = graphElim es nonKutVs
    _msg                = "graphElim: " ++ show (length es')

{- | `graphElim` "eliminates" a kvar k by replacing every "path"

          ki -> ci -> k -> c

      with an edge

          ki ------------> c
-}
graphElim :: [CEdge] -> S.HashSet F.KVar -> [CEdge]
graphElim es ks = ikvgEdges $ elimKs ks $ edgesIkvg es
  where
    elimKs      = flip (S.foldl' elimK)

elimK  :: IKVGraph -> F.KVar -> IKVGraph
elimK g k   = (g `addLinks` es') `delNodes` (kV : cis)
  where
   es'      = [(ki, c) | ki@(KVar _) <- kis, c@(Cstr _) <- cs]
   cs       = getSuccs g kV
   cis      = getPreds g kV
   kis      = concatMap (getPreds g) cis
   kV       = KVar k

--------------------------------------------------------------------------------
-- | Generic Dependencies ------------------------------------------------------
--------------------------------------------------------------------------------
data Elims a
  = Deps { depCuts    :: !(S.HashSet a)
         , depNonCuts :: !(S.HashSet a)
         }
    deriving (Show)

instance PPrint (Elims a) where
  pprintTidy _ d = "#Cuts ="    <+> ppSize (depCuts d) <+>
                   "#NonCuts =" <+> ppSize (depNonCuts d)
    where
      ppSize     = pprint . S.size

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
    ds          = edgeDeps cfg si es
    es          = kvEdges si

removeKutEdges ::  S.HashSet F.KVar -> [CEdge] -> [CEdge]
removeKutEdges ks = filter (not . isKut . snd)
  where
    cutVs         = S.map KVar ks
    isKut         = (`S.member` cutVs)

cutVars :: (F.TaggedC c a) => Config -> F.GInfo c a -> S.HashSet F.KVar
cutVars cfg si
  | autoKuts cfg = S.empty
  | otherwise    = F.ksVars . F.kuts $ si

forceKuts :: (Hashable a, Eq a) => S.HashSet a -> Elims a  -> Elims a
forceKuts xs (Deps cs ns) = Deps (S.union cs xs) (S.difference ns xs)

edgeDeps :: (F.TaggedC c a) => Config -> F.GInfo c a -> [CEdge] -> Elims F.KVar
edgeDeps cfg si  = forceKuts ks
                 . edgeDeps' cfg
                 . removeKutEdges ks
                 . filter isRealEdge
  where
    ks           = givenKs `S.union` nlKs
    givenKs      = cutVars cfg    si
    nlKs
      | nonLinCuts cfg = nonLinearKVars si
      | otherwise      = mempty

edgeDeps' :: Config -> [CEdge] -> Elims F.KVar
edgeDeps' cfg es = Deps (takeK cs) (takeK ns)
  where
    Deps cs ns   = gElims cfg kF cutF g
    g            = kvgEdges    (edgeGraph es)
    cutF         = edgeRankCut (edgeRank es)
    takeK        = sMapMaybe tx
    tx (KVar z)  = Just z
    tx _         = Nothing
    kF (KVar _)  = True
    kF _         = False

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
                      []  -> Nothing
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
gElims :: (Cutable a) => Config -> (a -> Bool) -> Cutter a -> [(a, a, [a])] -> Elims a
--------------------------------------------------------------------------------
gElims cfg kF cutF g = boundElims cfg kF g $ sccElims cutF g

--------------------------------------------------------------------------------
-- | `sccElims` returns an `Elims` that renders the dependency graph acyclic
--    by picking _at least one_ kvar from each non-trivial SCC in the graph
--------------------------------------------------------------------------------

sccElims :: (Cutable a) => Cutter a -> [(a, a, [a])] -> Elims a
sccElims f = sccsToDeps f . G.stronglyConnCompR

sccsToDeps :: (Cutable a) => Cutter a -> [G.SCC (a, a, [a])] -> Elims a
sccsToDeps f xs = mconcat $ sccDep f <$> xs

sccDep :: (Cutable a) =>  Cutter a -> G.SCC (a, a, [a]) -> Elims a
sccDep _ (G.AcyclicSCC (v,_,_)) = dNonCut v
sccDep f (G.CyclicSCC vs)      = cycleDep f vs

cycleDep :: (Cutable a) => Cutter a -> [(a, a, [a])] -> Elims a
cycleDep _ [] = mempty
cycleDep f vs = addCut f (f vs)

addCut :: (Cutable a) => Cutter a -> Maybe (a, [(a, a, [a])]) -> Elims a
addCut _ Nothing         = mempty
addCut f (Just (v, vs')) = mconcat $ dCut v : (sccDep f <$> sccs)
  where
    sccs                 = G.stronglyConnCompR vs'


--------------------------------------------------------------------------------
-- | `boundElims` extends the input `Elims` by adding kuts that ensure that
--   the *maximum distance* between an eliminated KVar and a cut KVar is
--   *upper bounded* by a given threshold.
--------------------------------------------------------------------------------
boundElims :: (Cutable a) => Config -> (a -> Bool) -> [(a, a, [a])] -> Elims a -> Elims a
--------------------------------------------------------------------------------
boundElims cfg isK es ds = maybe ds (bElims isK es ds) (elimBound cfg)

bElims :: (Cutable a) => (a -> Bool) -> [(a, a, [a])] -> Elims a -> Int -> Elims a
bElims isK es ds dMax   = forceKuts kS' ds
  where
    (_ , kS')           = L.foldl' step (M.empty, depCuts ds) vs
    vs                  = topoSort ds es
    predM               = invertEdges es
    addK v ks
      | isK v           = S.insert v ks
      | otherwise       = ks

    zero                = (0, S.empty)

    step (dM, kS) v
      | v `S.member` kS = (M.insert v zero  dM,        kS)
      | vDist < dMax    = (M.insert v dv    dM,        kS)
      | otherwise       = (M.insert v zero  dM, addK v kS)
      where
        dv              = trace msg dv_
        msg             = show v ++ " DIST =" ++ show vDist ++ " SIZE = " ++ show vSize
        dv_@(vDist, s)  = distV predM v dM
        vSize           = S.size s

distV :: (Cutable a) => M.HashMap a [a] -> a -> M.HashMap a (Int, S.HashSet a) -> (Int, S.HashSet a)
distV predM v dM = (d, s)
  where
    d            = 1 + maximumDef 0 (fst . du <$> us)
    s            = S.insert v (S.unions (snd . du <$> us))
    du u         = fromMaybe (oops u) $ M.lookup u dM
    us           = M.lookupDefault [] v predM
    oops u       = errorstar $ "dist: don't have dist for " ++ show u ++ " when checking " ++ show v

topoSort :: (Cutable a) => Elims a -> [(a, a, [a])] -> [a]
topoSort ds = G.flattenSCCs . reverse . G.stronglyConnComp . ripKuts ds

ripKuts :: (Cutable a) => Elims a -> [(a, a, [a])] -> [(a, a, [a])]
ripKuts ds es = [ (u, x, notKuts vs) | (u, x, vs) <- es ]
  where
    notKuts   = filter (not . (`S.member` ks))
    ks        = depCuts ds

invertEdges :: (Cutable a) => [(a, a, [a])] -> M.HashMap a [a]
invertEdges es = group [ (v, u) | (u, _, vs) <- es, v <- vs ]

maximumDef :: (Ord a) => a -> [a] -> a
maximumDef d [] = d
maximumDef _ xs = maximum xs


---------------------------------------------------------------------------
graphDeps :: F.TaggedC c a => F.GInfo c a -> [CEdge] -> CDeps
---------------------------------------------------------------------------
graphDeps fi cs = CDs { cSucc   = gSucc cg
                      , cPrev   = cPrevM
                      , cNumScc = gSccs cg
                      , cRank   = M.fromList [(i, rf i) | i <- is ]
                      }
  where
    rf          = rankF (F.cm fi) outRs inRs
    inRs        = inRanks fi es outRs
    outRs       = gRanks cg
    es          = gEdges cg
    cg          = cGraphCE cs
    is          = [i | (Cstr i, _) <- cs]
    cPrevM      = sortNub <$> group [ (i, k) | (KVar k, Cstr i) <- cs ]

--TODO merge these with cGraph and kvSucc
cGraphCE :: [CEdge] -> CGraph
cGraphCE cs = CGraph { gEdges = es
                     , gRanks = outRs
                     , gSucc  = next
                     , gSccs  = length sccs }
  where
    es             = [(i, i, M.lookupDefault [] i next) | (Cstr i, _) <- cs]
    next           = cSuccM cs
    (g, vf, _)     = G.graphFromEdges es
    (outRs, sccs)  = graphRanks g vf

cSuccM      :: [CEdge] -> CMap [F.SubcId]
cSuccM es    = (sortNub . concatMap kRdBy) <$> iWrites
  where
    kRdBy k  = M.lookupDefault [] k kReads
    iWrites  = group [ (i, k) | (Cstr i, KVar k) <- es ]
    kReads   = group [ (k, j) | (KVar k, Cstr j) <- es ]

rankF ::  F.TaggedC c a => CMap (c a) -> CMap Int -> CMap Int -> F.SubcId -> Rank
rankF cm outR inR = \i -> Rank (outScc i) (inScc i) (tag i)
  where
    outScc        = lookupCMap outR
    inScc         = lookupCMap inR
    tag           = F.stag . lookupCMap cm

---------------------------------------------------------------------------
inRanks ::  F.TaggedC c a => F.GInfo c a -> [DepEdge] -> CMap Int -> CMap Int
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
graphStatistics :: F.TaggedC c a => Config -> F.GInfo c a -> IO ()
--------------------------------------------------------------------------------
graphStatistics cfg si = when (elimStats cfg) $ do
  -- writeGraph f  (kvGraph si)
  writeEdges f es'
  appendFile f . ppc . ptable $ graphStats cfg si
  where
    f        = queryFile Dot cfg
    es'      = removeKutEdges (depCuts ds) es
    (es, ds) = elimVars cfg si
    ppc d    = showpp $ vcat [" ", " ", "/*", pprint d, "*/"]

data Stats = Stats {
    stNumKVCuts   :: !Int   -- ^ number of kvars whose removal makes deps acyclic
  , stNumKVNonLin :: !Int   -- ^ number of kvars that appear >= 2 in some LHS
  , stNumKVTotal  :: !Int   -- ^ number of kvars
  , stIsReducible :: !Bool  -- ^ is dep-graph reducible
  , stSetKVNonLin :: !(S.HashSet F.KVar) -- ^ set of non-linear kvars
  }

instance PTable Stats where
  ptable (Stats {..})  = DocTable [
      ("# KVars [Cut]"    , pprint stNumKVCuts)
    , ("# KVars [NonLin]" , pprint stNumKVNonLin)
    , ("# KVars [All]"    , pprint stNumKVTotal)
    , ("# Reducible"      , pprint stIsReducible)
    , ("KVars NonLin"     , pprint stSetKVNonLin)
    ]

graphStats :: F.TaggedC c a => Config -> F.GInfo c a -> Stats
graphStats cfg si = Stats {
    stNumKVCuts   = S.size $ F.tracepp "CUTS:" (depCuts d)
  , stNumKVNonLin = S.size  nlks
  , stNumKVTotal  = S.size (depCuts d) + S.size (depNonCuts d)
  , stIsReducible = isReducible si
  , stSetKVNonLin = nlks
  }
  where
    nlks          = nonLinearKVars si
    d             = snd $ elimVars cfg si

--------------------------------------------------------------------------------
nonLinearKVars :: (F.TaggedC c a) => F.GInfo c a -> S.HashSet F.KVar
--------------------------------------------------------------------------------
nonLinearKVars fi = S.unions $ nlKVarsC bs <$> cs
  where
    bs            = F.bs fi
    cs            = M.elems (F.cm fi)

nlKVarsC :: (F.TaggedC c a) => F.BindEnv -> c a -> S.HashSet F.KVar
nlKVarsC bs c = S.fromList [ k |  (k, n) <- V.envKVarsN bs c, n >= 2]
