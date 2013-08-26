{-@ LIQUID "--notermination" @-}
{-# LANGUAGE ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances #-}

-- Modified from Data.KMeans from http://hackage.haskell.org/package/kmeans

module KMeansNew (kmeans, kmeansGen) where

import KMeansHelper
import Prelude              hiding      (zipWith)
import Data.List                        (sort, span, minimumBy)
import Data.Function                    (on)
import Data.Ord                         (comparing)
import Language.Haskell.Liquid.Prelude  (liquidError, liquidAssume, liquidAssert)

{- Fixed Length Lists 

   type List a N = {v : [a] | (len v) = N}

   Non-empty Lists
   
   type NonEmptyList a = {v : [a] | (len v) > 0}

   N-Dimensional Points
   
   type Point N = List Double N

   Matrices
   
   type Matrix a Rows Cols = List (List a Cols) Rows

   groupBy   :: (a -> a -> Bool) -> [a] -> (Clustering a)
   partition :: PosInt -> [a] -> (Clustering a)
   zipWith   :: (a -> b -> c) -> xs:[a] -> (List b (len xs)) -> (List c (len xs))
   transpose :: c:Int -> r:PosInt -> Matrix a r c -> Matrix a c r

-}

-- | Generalized Points

data WrapType b a = WrapType {getVect :: b, getVal :: a}

instance Eq (WrapType [Double] a) where
   (==) = (==) `on` getVect

instance Ord (WrapType [Double] a) where
    compare = comparing getVect

{-@ type GenPoint a N  = WrapType (Point N) a @-}


-- | Algorithm: Iterative Clustering

{-@ kmeans' :: n:Int
            -> k:PosInt
            -> points:[(GenPoint a n)]
            -> (Clustering (GenPoint a n)) @-}


kmeans' n k points    = fixpoint (refineCluster n) initialClustering
  where
    initialClustering = partition clusterSize points
    clusterSize       = max 1 ((length points + k - 1) `div` k)

    fixpoint          :: (Eq a) => (a -> a) -> a -> a
    fixpoint f x      = if (f x) == x then x else fixpoint f (f x)

-- | Refining A Clustering

{-@ refineCluster :: n:Int
                  -> Clustering (GenPoint a n)
                  -> Clustering (GenPoint a n)          @-}

refineCluster n clusters = clusters'
  where
    -- 1. Compute cluster centers
    centers        = map (clusterCenter n) clusters

    -- 2. Map points to their nearest center
    points         = concat clusters
    centeredPoints = sort [(nearestCenter n p centers, p) | p <- points]

    -- 3. Group points by nearest center to get new clusters
    centeredGroups = groupBy ((==) `on` fst) centeredPoints
    clusters'      = map (map snd) centeredGroups


-- | Computing the Center of a Cluster

{-@ clusterCenter :: n:Int -> NonEmptyList (GenPoint a n) -> Point n @-}

clusterCenter n xs = map average xs'
  where
    numPoints      = length xs
    xs'            = transpose n numPoints (map getVect xs)

    average        :: [Double] -> Double
    average        = (`safeDiv` numPoints) . sum

safeDiv n 0 = liquidError "divide by zero"
safeDiv n d = n / (fromIntegralNZ d)

fromIntegralNZ = assumeNZ . fromIntegral . assertNZ
  where 
    assertNZ v = liquidAssert (v /= 0) v 
    assumeNZ v = liquidAssume (v /= 0) v


-- | Finding the Nearest Center

{-@ nearestCenter :: n:Int -> (GenPoint a n) -> [(Point n)] -> (Point n) @-}
nearestCenter     :: Int -> WrapType [Double] a -> [[Double]] -> [Double]
nearestCenter n x = minKey . map (\c -> (c, distance c (getVect x)))


minKey  :: (Ord v) => [(k, v)] -> k
minKey  = fst . minimumBy (\x y -> compare (snd x) (snd y))


distance     :: [Double] -> [Double] -> Double
distance a b = sqrt . sum $ zipWith (\v1 v2 -> (v1 - v2) ^ 2) a b


-- | Top-Level API

{-@ kmeansGen :: n:Int
              -> (a -> (Point n))
              -> k:PosInt
              -> xs:[a]
              -> (Clustering a)
  @-}

kmeansGen n project k = map (map getVal)
                      . kmeans' n k
                      . map (\x -> WrapType (project x) x)

{-@ kmeans :: n:Int
           -> k:PosInt
           -> points:[(Point n)]
           -> (Clustering (Point n))
  @-}

kmeans n   = kmeansGen n id

