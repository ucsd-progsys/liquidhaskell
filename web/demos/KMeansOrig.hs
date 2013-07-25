{--! run liquid with no-termination -}
{- |
Module      :  Data.KMeans
Copyright   :  (c) Keegan Carruthers-Smith, 2009
License     :  BSD 3 Clause
Maintainer  :  gershomb@gmail.com
Stability   :  experimental

A simple implementation of the standard k-means clustering algorithm: <http://en.wikipedia.org/wiki/K-means_clustering>. K-means clustering partitions points into clusters, with each point belonging to the cluster with th nearest mean. As the general problem is NP hard, the standard algorithm, which is relatively rapid, is heuristic and not guaranteed to converge to a global optimum. Varying the input order, from which the initial clusters are generated, can yield different results. For degenerate and malicious cases, the algorithm may take exponential time.

-}

{-# LANGUAGE ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances #-}

module Data.KMeans (kmeans, kmeansGen)
    where

-- import Data.List (transpose, sort, groupBy, minimumBy)
import Data.List (sort, span, minimumBy)
import Data.Function (on)
import Data.Ord (comparing)
import Language.Haskell.Liquid.Prelude (liquidAssume, liquidAssert, liquidError)

-- Liquid: Kept for exposition, can use Data.List.groupBy
{-@ assert groupBy :: (a -> a -> Bool) -> [a] -> [{v:[a] | len(v) > 0}] @-}
groupBy                 :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy _  []           =  []
groupBy eq (x:xs)       =  (x:ys) : groupBy eq zs
                           where (ys,zs) = span (eq x) xs

{-@ assert transpose :: n:Int
                     -> m:{v:Int | v > 0} 
                     -> {v:[{v:[a] | len(v) = n}] | len(v) = m} 
                     -> {v:[{v:[a] | len(v) = m}] | len(v) = n} 
  @-}

transpose :: Int -> Int -> [[a]] -> [[a]]
transpose 0 _ _              = []
transpose n m ((x:xs) : xss) = (x : map head xss) : transpose (n - 1) m (xs : map tail xss)
transpose n m ([] : _)       = liquidError "transpose1" 
transpose n m []             = liquidError "transpose2"

data WrapType b a = WrapType {getVect :: b, getVal :: a}

instance Eq (WrapType [Double] a) where
   (==) = (==) `on` getVect

instance Ord (WrapType [Double] a) where
    compare = comparing getVect

-- dist ::  [Double] -> [Double] -> Double 
dist a b = sqrt . sum $ zipWith (\x y-> (x-y) ^ 2) a b      -- Liquid: zipWith dimensions

centroid n points = map (( / l) . sum) points'              -- Liquid: Divide By Zero
    where 
      l  = fromIntegralNZ m 
      m  = length points 
      points' = transpose n m (map getVect points)

fromIntegralNZ = assumeNZ . fromIntegral . assertNZ
  where 
    assertNZ v = liquidAssert (v /= 0) v 
    assumeNZ v = liquidAssume (v /= 0) v




closest (n :: Int) points point = minimumBy (comparing $ dist point) points

recluster' n centroids points = map (map snd) $ groupBy ((==) `on` fst) reclustered
    where reclustered = sort [(closest n centroids (getVect a), a) | a <- points]

recluster n clusters = recluster' n centroids $ concat clusters
    where centroids = map (centroid n) clusters

--part :: (Eq a) => Int -> [a] -> [[a]]
--part x ys
--     | zs' == [] = [zs]
--     | otherwise = zs : part x zs'
--    where (zs, zs') = splitAt x ys

{-@ assert part :: n:{v:Int | v > 0} -> [a] -> [{v:[a] | len(v) > 0}] @-}
part n []       = []
part n ys@(_:_) = zs : part n zs' 
                  where zs  = take n ys
                        zs' = drop n ys

-- | Recluster points
kmeans'' n clusters
    | clusters == clusters' = clusters
    | otherwise             = kmeans'' n clusters'
    where clusters' = recluster n clusters

kmeans' n k points = kmeans'' n $ part l points
    where l = max 1 ((length points + k - 1) `div` k)

-- | Cluster points in a Euclidian space, represented as lists of Doubles, into at most k clusters.
-- The initial clusters are chosen arbitrarily.
{-@ assert kmeans :: n: Int -> k:Int -> points:[{v:[Double] | len(v) = n}] -> [[{ v: [Double] | len(v) = n}]] @-}
kmeans :: Int -> Int -> [[Double]] -> [[[Double]]]
kmeans n = kmeansGen n id

-- | A generalized kmeans function. This function operates not on points, but an arbitrary type which may be projected into a Euclidian space. Since the projection may be chosen freely, this allows for weighting dimensions to different degrees, etc.
{-@ assert kmeansGen :: n: Int -> f:(a -> {v:[Double] | len(v) = n }) -> k:Int -> points:[a] -> [[a]] @-}
kmeansGen :: Int -> (a -> [Double]) -> Int -> [a] -> [[a]]
kmeansGen n f k points = map (map getVal) . kmeans' n k . map (\x -> WrapType (f x) x) $ points














