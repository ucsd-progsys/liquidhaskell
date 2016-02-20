{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- | This module implements functions to build constraint / kvar
--   dependency graphs, partition them and print statistics about
--   their structure.

module Language.Fixpoint.Partition (

  -- * Split constraints
    CPart (..)
  , partition, partition', partitionN

  -- * Information about cores
  , MCInfo (..)
  , mcInfo

  -- * Queries over dependencies
  , graphStatistics
  , GDeps (..)
  , deps
  -- , isReducible

  -- * Debug
  , elimSolGraph
  ) where

import           GHC.Conc                  (getNumProcessors)
import           Control.Monad             (when, forM_)
-- import           GHC.Generics              (Generic)
import           Language.Fixpoint.Misc         -- hiding (group)
import           Language.Fixpoint.Utils.Files
import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.Types.PrettyPrint
import qualified Language.Fixpoint.Types.Visitor      as V
import qualified Language.Fixpoint.Solver.Solution    as So
import qualified Language.Fixpoint.Types              as F
import           Language.Fixpoint.Types.Graphs
import qualified Data.HashMap.Strict                  as M
import qualified Data.Graph                           as G
import qualified Data.Tree                            as T
import           Data.Function (on)
import           Data.Maybe                     (mapMaybe, fromMaybe)
import           Data.Hashable
import           Text.PrettyPrint.HughesPJ
import           Data.List (sortBy)
import qualified Data.HashSet              as S

import Data.Graph.Inductive



--------------------------------------------------------------------------------
-- | Constraint Partition Container --------------------------------------------
--------------------------------------------------------------------------------

data CPart a = CPart { pws :: M.HashMap F.KVar (F.WfC a)
                     , pcm :: M.HashMap Integer (F.SubC a)
                     , cFileName :: FilePath
                     }

instance Monoid (CPart a) where
   mempty = CPart mempty mempty mempty
   mappend l r = CPart { pws = pws l `mappend` pws r
                       , pcm = pcm l `mappend` pcm r
                       , cFileName = cFileName l
                       }

--------------------------------------------------------------------------------
-- | Multicore info ------------------------------------------------------------
--------------------------------------------------------------------------------

data MCInfo = MCInfo { mcCores :: Int
                     , mcMinPartSize :: Int
                     , mcMaxPartSize :: Int
                     } deriving (Show)

mcInfo :: Config -> IO MCInfo
mcInfo c = do
   np <- getNumProcessors
   let nc = fromMaybe np (cores c)
   return MCInfo { mcCores = nc
                 , mcMinPartSize = minPartSize c
                 , mcMaxPartSize = maxPartSize c
                 }

partition :: (F.Fixpoint a) => Config -> F.FInfo a -> IO (F.Result (Integer, a))
partition cfg fi
  = do dumpPartitions cfg fis
       writeGraph      f   g
       return mempty
    where
      f        = queryFile Dot cfg
      (g, fis) = partition' Nothing fi

------------------------------------------------------------------------------
-- | Partition an FInfo into multiple disjoint FInfos
------------------------------------------------------------------------------
partition' :: Maybe MCInfo -- ^ Nothing to produce the maximum possible
                             -- number of partitions. Or a MultiCore Info
                             -- to control the partitioning
           -> F.FInfo a -> (KVGraph, [F.FInfo a])
------------------------------------------------------------------------------
partition' mn fi  = case mn of
   Nothing -> (g, fis mkPartition id)
   Just mi -> (g, partitionN mi fi $ fis mkPartition' finfoToCpart)
  where
    g              = kvGraph   fi
    css            = decompose g
    fis partF ctor = applyNonNull [ctor fi] (pbc partF) css
    pbc partF      = partitionByConstraints partF fi


-- | Partition an FInfo into a specific number of partitions of roughly equal
-- amounts of work
partitionN :: MCInfo    -- ^ describes thresholds and partiton amounts
           -> F.FInfo a   -- ^ The originial FInfo
           -> [CPart a] -- ^ A list of the smallest possible CParts
           -> [F.FInfo a] -- ^ At most N partitions of at least thresh work
partitionN mi fi cp
   | cpartSize (finfoToCpart fi) <= minThresh = [fi]
   | otherwise = map (cpartToFinfo fi) $ toNParts sortedParts
   where
      toNParts p
         | isDone p = p
         | otherwise = toNParts $ insertSorted firstTwo rest
            where (firstTwo, rest) = unionFirstTwo p
      isDone [] = True
      isDone [_] = True
      isDone fi'@(a:b:_) = length fi' <= prts
                            && (cpartSize a >= minThresh
                                || cpartSize a + cpartSize b >= maxThresh)
      sortedParts = sortBy sortPredicate cp
      unionFirstTwo (a:b:xs) = (a `mappend` b, xs)
      unionFirstTwo _        = errorstar "Partition.partitionN.unionFirstTwo called on bad arguments"
      sortPredicate lhs rhs
         | cpartSize lhs < cpartSize rhs = GT
         | cpartSize lhs > cpartSize rhs = LT
         | otherwise = EQ
      insertSorted a []     = [a]
      insertSorted a (x:xs) = if sortPredicate a x == LT
                              then x : insertSorted a xs
                              else a : x : xs
      prts      = mcCores mi
      minThresh = mcMinPartSize mi
      maxThresh = mcMaxPartSize mi


-- | Return the "size" of a CPart. Used to determine if it's
-- substantial enough to be worth parallelizing.
cpartSize :: CPart a -> Int
cpartSize c = (M.size . pcm) c + (length . pws) c

-- | Convert a CPart to an FInfo
cpartToFinfo :: F.FInfo a -> CPart a -> F.FInfo a
cpartToFinfo fi p = fi { F.cm = pcm p
                       , F.ws = pws p
                       , F.fileName = cFileName p
                       }

-- | Convert an FInfo to a CPart
finfoToCpart :: F.FInfo a -> CPart a
finfoToCpart fi = CPart { pcm = F.cm fi
                        , pws = F.ws fi
                        , cFileName = F.fileName fi
                        }

-------------------------------------------------------------------------------------
dumpPartitions :: (F.Fixpoint a) => Config -> [F.FInfo a] -> IO ()
-------------------------------------------------------------------------------------
dumpPartitions cfg fis =
  forM_ (zip [0..] fis) $ \(i, fi) ->
    writeFile (partFile fi i) (render $ F.toFixpoint cfg fi)

partFile :: F.FInfo a -> Int -> FilePath
partFile fi j = extFileName (Part j) (F.fileName fi)


-- | Type alias for a function to construct a partition. mkPartition and
-- mkPartition' are the two primary functions that conform to this interface
type PartitionCtor a b = F.FInfo a
                         -> M.HashMap Int [(Integer, F.SubC a)]
                         -> M.HashMap Int [(F.KVar, F.WfC a)]
                         -> Int
                         -> b -- ^ typically a F.FInfo a or F.CPart a

partitionByConstraints :: PartitionCtor a b -- ^ mkPartition or mkPartition'
                          -> F.FInfo a
                          -> KVComps
                          -> ListNE b -- ^ [F.FInfo a] or [F.CPart a]
partitionByConstraints f fi kvss = f fi icM iwM <$> js
  where
    js   = fst <$> jkvs                                -- groups
    gc   = groupFun cM                                 -- (i, ci) |-> j
    gk   = groupFun kM                                 -- k       |-> j

    iwM  = groupMap (gk . fst) (M.toList (F.ws fi))             -- j |-> [w]
    icM  = groupMap (gc . fst) (M.toList (F.cm fi))  -- j |-> [(i, ci)]

    jkvs = zip [1..] kvss
    kvI  = [ (x, j) | (j, kvs) <- jkvs, x <- kvs ]
    kM   = M.fromList [ (k, i) | (KVar k, i) <- kvI ]
    cM   = M.fromList [ (c, i) | (Cstr c, i) <- kvI ]

mkPartition fi icM iwM j
  = fi { F.cm       = M.fromList $ M.lookupDefault [] j icM
       , F.ws       = M.fromList $ M.lookupDefault [] j iwM
       , F.fileName = partFile fi j
       }

mkPartition' fi icM iwM j
  = CPart { pcm       = M.fromList $ M.lookupDefault [] j icM
          , pws       = M.fromList $ M.lookupDefault [] j iwM
          , cFileName = partFile fi j
          }

groupFun :: (Show k, Eq k, Hashable k) => M.HashMap k Int -> k -> Int
groupFun m k = safeLookup ("groupFun: " ++ show k) k m


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
deps :: (F.TaggedC c a) => F.GInfo c a -> GDeps F.KVar
--------------------------------------------------------------------------------
deps si         = Deps (takeK cs) (takeK ns)
  where
    Deps cs ns  = gDeps cutF (edgeGraph es)
    es          = kvEdges si
    -- ORIG cutF = chooseCut isK (cuts si)
    cutF        = edgeRankCut (edgeRank es)
    takeK       = sMapMaybe tx
    tx (KVar z) = Just z
    tx _        = Nothing

-- crash _ = undefined
-- cutter :: F.TaggedC c a => F.GInfo c a -> Cutter CVertex
-- cutter si = chooseCut isK (cuts si)

-- ORIG isK :: CVertex -> Bool
-- ORIG isK (KVar _) = True
-- ORIG isK _        = False
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
    orderBy       = sortBy (compare `on` rank)

--------------------------------------------------------------------------------
type Cutter a = [(a, a, [a])] -> Maybe (a, [(a, a, [a])])
--------------------------------------------------------------------------------
-- ORIG chooseCut :: (Cutable a) => (a -> Bool) -> S.HashSet a -> Cutter a
-- ORIG --------------------------------------------------------------------------------
-- ORIG chooseCut f ks vs = case vs'' of
                      -- ORIG []  -> Nothing
                      -- ORIG v:_ -> Just (v, [x | x@(u,_,_) <- vs, u /= v])
  -- ORIG where
    -- ORIG vs'           = [x | (x,_,_) <- vs, f x]
    -- ORIG is            = S.intersection (S.fromList vs') ks
    -- ORIG vs''          = if S.null is then vs' else S.toList is
       -- ORIG -- ^ -- we select a RANDOM element,
       -- ORIG ------- instead pick the "first" element.



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

--------------------------------------------------------------------------------
isReducible :: F.SInfo a -> Bool
--------------------------------------------------------------------------------
isReducible fi = all (isReducibleWithStart g) vs
  where
    g  = convertToGraph fi
    vs = {- trace (showDot $ fglToDotGeneric g show (const "") id) -} nodes g

isReducibleWithStart :: Gr a b -> Node -> Bool
isReducibleWithStart g x = all (isBackEdge domList) rEdges
  where
    dfsTree = head $ dff [x] g --head because only care about nodes reachable from 'start node'?
    rEdges = [e | e@(a,b) <- edges g, isDescendant a b dfsTree]
    domList = dom g x

convertToGraph :: F.SInfo a -> Gr Int ()
convertToGraph fi = mkGraph vs es
  where
    subCs        = M.elems (F.cm fi)
    es           = lUEdge <$> concatMap (subcEdges' kvI $ F.bs fi) subCs
    ks           = M.keys (F.ws fi)
    kiM          = M.fromList $ zip ks [0..]
    kvI k        = safeLookup ("convertToGraph: " ++ show k) k kiM
    vs           = lNode . kvI <$> M.keys (F.ws fi)
    lNode i      = (i, i)
    lUEdge (i,j) = (i, j, ())

isDescendant :: Node -> Node -> T.Tree Node -> Bool
isDescendant x y (T.Node z f) | z == y    = f `contains` x
                              | z == x    = False
                              | otherwise = any (isDescendant x y) f

contains :: [T.Tree Node] -> Node -> Bool
contains t x = x `elem` concatMap T.flatten t

isBackEdge :: [(Node, [Node])] -> Edge -> Bool
isBackEdge t (u,v) = v `elem` xs
  where
    (Just xs) = lookup u t

subcEdges' :: (F.KVar -> Node) -> F.BindEnv -> F.SimpC a -> [(Node, Node)]
subcEdges' kvI be c = [(kvI k1, kvI k2) | k1 <- V.envKVars be c
                                        , k2 <- V.kvars $ F.crhs c]

--------------------------------------------------------------------------------
graphStatistics :: Config -> F.SInfo a -> IO ()
--------------------------------------------------------------------------------
graphStatistics cfg si = when (elimStats cfg) $ do
  writeGraph f  (kvGraph si)
  appendFile f . ppc . ptable $ graphStats si
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

graphStats :: F.SInfo a -> Stats
graphStats si     = Stats {
    stNumKVCuts   = S.size (depCuts d)
  , stNumKVNonLin = S.size  nlks
  , stNumKVTotal  = S.size (depCuts d) + S.size (depNonCuts d)
  , stIsReducible = isReducible si
  , stSetKVNonLin = nlks
  }
  where
    nlks          = nlKVars si
    d             = deps si

nlKVars :: (F.TaggedC c a) => F.GInfo c a -> S.HashSet F.KVar
nlKVars fi = S.unions $ nlKVarsC bs <$> cs
  where
    bs     = F.bs fi
    cs     = M.elems (F.cm fi)

nlKVarsC :: (F.TaggedC c a) => F.BindEnv -> c a -> S.HashSet F.KVar
nlKVarsC bs c = S.fromList [ k |  (k, n) <- V.envKVarsN bs c, n >= 2]

--------------------------------------------------------------------------------
-- | Build and print the graph of post eliminate solution, which has an edge
--   from k -> k' if k' appears directly inside the "solution" for k
--------------------------------------------------------------------------------
elimSolGraph :: Config -> F.Solution -> IO ()
elimSolGraph cfg s = writeGraph f (So.solutionGraph s)
  where
    f              = queryFile Dot cfg
