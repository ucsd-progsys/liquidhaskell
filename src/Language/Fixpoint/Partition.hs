{-# LANGUAGE DeriveGeneric #-}

-- | This module implements functions that print out
--   statistics about the constraints.

module Language.Fixpoint.Partition (partition, partition', partitionN) where

import           Control.Monad (forM_)
import           GHC.Generics                   (Generic)
import           Language.Fixpoint.Misc         hiding (group)-- (fst3, safeLookup, mlookup, groupList)
import           Language.Fixpoint.Files
import           Language.Fixpoint.Config
import           Language.Fixpoint.PrettyPrint
import qualified Language.Fixpoint.Visitor      as V
import qualified Language.Fixpoint.Types        as F
import qualified Data.HashMap.Strict            as M
import qualified Data.List                      as L
import qualified Data.Graph                     as G
import qualified Data.Tree                      as T
import           Data.Hashable
import           Text.PrettyPrint.HughesPJ
import           Data.List (sortBy)

partition :: (F.Fixpoint a) => Config -> F.FInfo a -> IO (F.Result a)
partition cfg fi
  = do dumpPartitions cfg fis
       dumpEdges      cfg es
       -- writeLoud $ render $ ppGraph es
       return mempty
    where
       (es, fis) = partition' Nothing fi

-- | Partition an FInfo into multiple disjoint FInfos
partition' :: Maybe F.MCInfo -- ^ Nothing to produce the maximum possible
                             -- number of partitions. Or a MultiCore Info
                             -- to control the partitioning
           -> F.FInfo a -> (KVGraph, [F.FInfo a])
partition' mn fi  = case mn of
   Nothing -> (g, fis mkPartition id)
   (Just mi) -> (g, partitionN mi fi $ fis mkPartition' finfoToCpart)
  where
    es             = kvEdges   fi
    g              = kvGraph   es
    css            = decompose g
    fis partF ctor = applyNonNull [ctor fi]
                                  (partitionByConstraints
                                   partF
                                   fi) css


-- | Partition an FInfo into a specific number of partitions of roughly equal
-- amounts of work
partitionN :: F.MCInfo -- ^ describes thresholds and partiton amounts
              -> F.FInfo a -- ^ The originial FInfo
              -> [F.CPart a] -- ^ A list of the smallest possible CParts
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
      sortPredicate lhs rhs
         | cpartSize lhs < cpartSize rhs = GT
         | cpartSize lhs > cpartSize rhs = LT
         | otherwise = EQ
      insertSorted a [] = [a]
      insertSorted a (x:xs) = if sortPredicate a x == LT
                              then x : insertSorted a xs
                              else a:x:xs
      prts = F.mcCores mi
      minThresh = F.mcMinPartSize mi
      maxThresh = F.mcMaxPartSize mi


-- | Return the "size" of a CPart. Used to determine if it's
-- substantial enough to be worth parallelizing.
cpartSize :: F.CPart a -> Int
cpartSize c = (M.size . F.pcm) c + (length . F.pws) c

-- | Convert a CPart to an FInfo
cpartToFinfo :: F.FInfo a -> F.CPart a -> F.FInfo a
cpartToFinfo fi p = fi { F.cm = F.pcm p
                       , F.ws = F.pws p
                       , F.fileName = F.cFileName p
                       }

-- | Convert an FInfo to a CPart
finfoToCpart :: F.FInfo a -> F.CPart a
finfoToCpart fi = F.CPart { F.pcm = F.cm fi
                          , F.pws = F.ws fi
                          , F.cFileName = F.fileName fi
                          }

-------------------------------------------------------------------------------------
dumpPartitions :: (F.Fixpoint a) => Config -> [F.FInfo a] -> IO ()
-------------------------------------------------------------------------------------
dumpPartitions cfg fis =
  forM_ fis $ \fi ->
    writeFile (F.fileName fi) (render $ F.toFixpoint cfg fi)

partFile :: F.FInfo a -> Int -> FilePath
partFile fi j = {- trace ("partFile: " ++ fjq) -} fjq
  where
    fjq = extFileName (Part j) (F.fileName fi)

-------------------------------------------------------------------------------------
dumpEdges :: Config -> KVGraph -> IO ()
-------------------------------------------------------------------------------------
dumpEdges cfg = writeFile f . render . ppGraph
  where
    f         = extFileName Dot (inFile cfg)

ppGraph :: KVGraph -> Doc
ppGraph g = ppEdges [ (v, v') | (v,_,vs) <- g, v' <- vs]

ppEdges :: [CEdge] -> Doc
ppEdges es = vcat [pprint v <+> text "-->" <+> pprint v' | (v, v') <- es]

-- | Type alias for a function to construct a partition. mkPartition and
-- mkPartition' are the two primary functions that conform to this interface
type PartitionCtor a b = F.FInfo a
                         -> M.HashMap Int [(Integer, F.SubC a)]
                         -> M.HashMap Int [F.WfC a]
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

    iwM  = maybeGroupMap (wfGroup gk) (F.ws fi)             -- j |-> [w]
    icM  = groupMap (gc . fst)   (M.toList (F.cm fi))  -- j |-> [(i, ci)]

    jkvs = zip [1..] kvss
    kvI  = [ (x, j) | (j, kvs) <- jkvs, x <- kvs ]
    kM   = M.fromList [ (k, i) | (KVar k, i) <- kvI ]
    cM   = M.fromList [ (c, i) | (Cstr c, i) <- kvI ]

mkPartition fi icM iwM j
  = fi { F.cm = M.fromList $ M.lookupDefault [] j icM
       , F.ws =              M.lookupDefault [] j iwM
       , F.fileName = partFile fi j
       }

mkPartition' fi icM iwM j
  = F.CPart { F.pcm = M.fromList $ M.lookupDefault [] j icM
            , F.pws = M.lookupDefault [] j iwM
            , F.cFileName = partFile fi j
            }

wfGroup gk w = case sortNub [gk k | k <- wfKvars w ] of
                 [i] -> Just i
                 _   -> Nothing


wfKvars :: F.WfC a -> [F.KVar]
wfKvars = V.kvars . F.sr_reft . F.wrft

-- | Version of Misc's inserts that handles Maybe keys. If the key is
-- Nothing, the value is not inserted
maybeInserts Nothing _ m = m
maybeInserts (Just k) v m = inserts k v m

maybeGroupMap f = L.foldl' (\m x -> maybeInserts (f x) x m) M.empty

groupFun :: (Show k, Eq k, Hashable k) => M.HashMap k Int -> k -> Int
groupFun m k = safeLookup ("groupFun: " ++ show k) k m

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

data CVertex = KVar F.KVar
             | Cstr Integer
               deriving (Eq, Ord, Show, Generic)

instance PPrint CVertex where
  pprint (KVar k) = pprint k
  pprint (Cstr i) = text "id:" <+> pprint i

instance Hashable CVertex

type CEdge    = (CVertex, CVertex)
type KVGraph  = [(CVertex, CVertex, [CVertex])]

type Comps a  = [[a]]
type KVComps  = Comps CVertex

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
decompose :: KVGraph -> KVComps
-------------------------------------------------------------------------------------
decompose kg = map (fst3 . f) <$> vss
  where
    (g,f,_)  = G.graphFromEdges kg
    vss      = T.flatten <$> G.components g

kvGraph :: [CEdge] -> KVGraph
kvGraph es = [(v,v,vs) | (v, vs) <- groupList es ]

kvEdges :: F.FInfo a -> [CEdge]
kvEdges fi = selfes ++ concatMap (subcEdges bs) cs
  where
    bs     = F.bs fi
    cs     = M.elems (F.cm fi)
    selfes = [(Cstr i, Cstr i) | c <- cs, let i = F.subcId c] ++
             [(KVar k, KVar k) | k <- fiKVars fi]

fiKVars :: F.FInfo a -> [F.KVar]
fiKVars fi = sortNub $ concatMap wfKvars (F.ws fi)


subcEdges :: F.BindEnv -> F.SubC a -> [CEdge]
subcEdges bs c =  [(KVar k, Cstr i ) | k  <- V.lhsKVars bs c]
               ++ [(Cstr i, KVar k') | k' <- V.rhsKVars c ]
  where
    i          = F.subcId c
