{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE OverloadedStrings #-}

-- | This module implements functions to build constraint / kvar
--   dependency graphs, partition them and print statistics about
--   their structure.

module Language.Fixpoint.Graph.Partition (

  -- * Split constraints
    CPart (..)
  , partition, partition', partitionN

  -- * Information about cores
  , MCInfo (..)
  , mcInfo

  -- * Debug
  , dumpPartitions

  ) where

import           GHC.Conc                  (getNumProcessors)
import           Control.Monad             (forM_)
-- import           GHC.Generics              (Generic)
import           Language.Fixpoint.Misc         -- hiding (group)
import           Language.Fixpoint.Utils.Files
import           Language.Fixpoint.Types.Config
-- import           Language.Fixpoint.Types.PrettyPrint
-- import qualified Language.Fixpoint.Types.Visitor      as V
import qualified Language.Fixpoint.Types              as F
import           Language.Fixpoint.Graph.Types
import           Language.Fixpoint.Graph.Deps

import qualified Data.HashMap.Strict                  as M
-- import qualified Data.Graph                           as G
-- import qualified Data.Tree                            as T
-- import           Data.Function (on)
import           Data.Maybe                     (fromMaybe)
import           Data.Hashable
import           Text.PrettyPrint.HughesPJ
import           Data.List (sortBy)
-- import qualified Data.HashSet              as S

-- import qualified Language.Fixpoint.Solver.Solution    as So
-- import Data.Graph.Inductive



--------------------------------------------------------------------------------
-- | Constraint Partition Container --------------------------------------------
--------------------------------------------------------------------------------

data CPart c a = CPart { pws :: !(M.HashMap F.KVar (F.WfC a))
                       , pcm :: !(M.HashMap Integer (c a))
                       }
  
instance Monoid (CPart c a) where
   mempty      = CPart mempty mempty
   mappend l r = CPart { pws = pws l `mappend` pws r
                       , pcm = pcm l `mappend` pcm r
                       }

--------------------------------------------------------------------------------
-- | Multicore info ------------------------------------------------------------
--------------------------------------------------------------------------------

data MCInfo = MCInfo { mcCores       :: !Int
                     , mcMinPartSize :: !Int
                     , mcMaxPartSize :: !Int
                     } deriving (Show)

mcInfo :: Config -> IO MCInfo
mcInfo c = do
   np <- getNumProcessors
   let nc = fromMaybe np (cores c)
   return MCInfo { mcCores = nc
                 , mcMinPartSize = minPartSize c
                 , mcMaxPartSize = maxPartSize c
                 }

partition :: (F.Fixpoint a, F.Fixpoint (c a), F.TaggedC c a) => Config -> F.GInfo c a -> IO (F.Result (Integer, a))
partition cfg fi
  = do dumpPartitions cfg fis
       -- writeGraph      f   g
       return mempty
    where
      --f   = queryFile Dot cfg
      fis = partition' Nothing fi

------------------------------------------------------------------------------
-- | Partition an FInfo into multiple disjoint FInfos. Info is Nothing to
--   produce the maximum possible number of partitions. Or a MultiCore Info
--   to control the partitioning
------------------------------------------------------------------------------
partition' :: (F.TaggedC c a) 
           => Maybe MCInfo -> F.GInfo c a -> [F.GInfo c a]
------------------------------------------------------------------------------
partition' mn fi  = case mn of
   Nothing -> fis mkPartition id
   Just mi -> partitionN mi fi $ fis mkPartition' finfoToCpart
  where
    css            = decompose fi
    fis partF ctor = applyNonNull [ctor fi] (pbc partF) css
    pbc partF      = partitionByConstraints partF fi

-- | Partition an FInfo into a specific number of partitions of roughly equal
-- amounts of work
partitionN :: MCInfo        -- ^ describes thresholds and partiton amounts
           -> F.GInfo c a   -- ^ The originial FInfo
           -> [CPart c a]   -- ^ A list of the smallest possible CParts
           -> [F.GInfo c a] -- ^ At most N partitions of at least thresh work
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
cpartSize :: CPart c a -> Int
cpartSize c = (M.size . pcm) c + (length . pws) c

-- | Convert a CPart to an FInfo
cpartToFinfo :: F.GInfo c a -> CPart c a -> F.GInfo c a
cpartToFinfo fi p = fi {F.ws = pws p, F.cm = pcm p} 

-- | Convert an FInfo to a CPart
finfoToCpart :: F.GInfo c a -> CPart c a
finfoToCpart fi = CPart { pcm = F.cm fi
                        , pws = F.ws fi
                        }

-------------------------------------------------------------------------------------
dumpPartitions :: (F.Fixpoint (c a), F.Fixpoint a) => Config -> [F.GInfo c a] -> IO ()
-------------------------------------------------------------------------------------
dumpPartitions cfg fis =
  forM_ (zip [0..] fis) $ \(i, fi) ->
    writeFile (queryFile (Part i) cfg) (render $ F.toFixpoint cfg fi)


-- | Type alias for a function to construct a partition. mkPartition and
--   mkPartition' are the two primary functions that conform to this interface
type PartitionCtor c a b = F.GInfo c a
                       -> M.HashMap Int [(Integer, c a)]
                       -> M.HashMap Int [(F.KVar, F.WfC a)]
                       -> Int
                       -> b -- ^ typically a F.FInfo a or F.CPart a

partitionByConstraints :: PartitionCtor c a b -- ^ mkPartition or mkPartition'
                       -> F.GInfo c a
                       -> KVComps
                       -> ListNE b          -- ^ [F.FInfo a] or [F.CPart a]
partitionByConstraints f fi kvss = f fi icM iwM <$> js
  where
    js   = fst <$> jkvs                                -- groups
    gc   = groupFun cM                                 -- (i, ci) |-> j
    gk   = groupFun kM                                 -- k       |-> j

    iwM  = groupMap (gk . fst) (M.toList (F.ws fi))    -- j |-> [w]
    icM  = groupMap (gc . fst) (M.toList (F.cm fi))    -- j |-> [(i, ci)]

    jkvs = zip [1..] kvss
    kvI  = [ (x, j) | (j, kvs) <- jkvs, x <- kvs ]
    kM   = M.fromList [ (k, i) | (KVar k, i) <- kvI ]
    cM   = M.fromList [ (c, i) | (Cstr c, i) <- kvI ]

mkPartition :: F.GInfo c a
            -> M.HashMap Int [(Integer, c a)]
            -> M.HashMap Int [(F.KVar, F.WfC a)]
            -> Int
            -> F.GInfo c a
mkPartition fi icM iwM j
  = fi{ F.cm       = M.fromList $ M.lookupDefault [] j icM
      , F.ws       = M.fromList $ M.lookupDefault [] j iwM
      }

mkPartition' :: F.GInfo c a
             -> M.HashMap Int [(Integer, c a)]
             -> M.HashMap Int [(F.KVar, F.WfC a)]
             -> Int
             -> CPart c a
mkPartition' _ icM iwM j
  = CPart { pcm       = M.fromList $ M.lookupDefault [] j icM
          , pws       = M.fromList $ M.lookupDefault [] j iwM
          }

groupFun :: (Show k, Eq k, Hashable k) => M.HashMap k Int -> k -> Int
groupFun m k = safeLookup ("groupFun: " ++ show k) k m
