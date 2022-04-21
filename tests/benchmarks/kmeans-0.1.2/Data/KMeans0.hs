{- |
Module      :  Data.KMeans
Copyright   :  (c) Keegan Carruthers-Smith, 2009
License     :  BSD 3 Clause
Maintainer  :  gershomb@gmail.com
Stability   :  experimental

A simple implementation of the standard k-means clustering algorithm: <http://en.wikipedia.org/wiki/K-means_clustering>. K-means clustering partitions points into clusters, with each point belonging to the cluster with th nearest mean. As the general problem is NP hard, the standard algorithm, which is relatively rapid, is heuristic and not guaranteed to converge to a global optimum. Varying the input order, from which the initial clusters are generated, can yield different results. For degenerate and malicious cases, the algorithm may take exponential time.

-}

{-# LANGUAGE ScopedTypeVariables #-}

module Data.KMeans (kmeans)
    where

import Data.List (sort, groupBy, minimumBy)
import Data.Function (on)
import Data.Ord (comparing)

import Language.Haskell.Liquid.List (transpose)

dist ::  [Double] -> [Double] -> Double 
dist a b = sqrt . sum $ zipWith (\x y-> (x-y) ^ 2) a b

centroid ::  Int -> [[Double]] -> [Double]
centroid n points = map (flip (/) l . sum) $ transpose n points
    where l = fromIntegral $ length points

closest ::  Int -> [[Double]] -> [Double] -> [Double]
closest n points point = minimumBy (comparing $ dist point) points

recluster' :: Int -> [[Double]] -> [[Double]] -> [[[Double]]]
recluster' n centroids points = map (map snd) $ groupBy ((==) `on` fst) reclustered
    where reclustered = sort [(closest n centroids a, a) | a <- points]

recluster :: Int -> [[[Double]]] -> [[[Double]]]
recluster n clusters = recluster' n centroids $ concat clusters
    where centroids = map (centroid n) clusters

part :: (Eq a) => Int -> [a] -> [[a]]
part x ys
     | zs' == [] = [zs]
     | otherwise = zs : part x zs'
    where (zs, zs') = splitAt x ys

-- | Recluster points
kmeans'' n clusters
    | clusters == clusters' = clusters
    | otherwise             = kmeans'' n clusters'
    where clusters' = recluster n clusters

--blocker :: Int -> Int -> [[Double]] -> [[[Double]]]
--blocker n l points = part l points

kmeans' n k points = kmeans'' n $ part l points
    where l = (length points + k - 1) `div` k

-- | Cluster points in a Euclidian space, represented as lists of Doubles, into at most k clusters.
-- The initial clusters are chosen arbitrarily.
{-# ANN kmeans "n: Int -> k:Int -> points:[{v:[Double] | len(v) = n}] -> [[{ v: [Double] | len(v) = n}]]" #-}
kmeans :: Int -> Int -> [[Double]] -> [[[Double]]]
--kmeans n k points = kmeans' n k points
kmeans n = kmeansGen n id

-- | A generalized kmeans function. This function operates not on points, but an arbitrary type which may be projected into a Euclidian space. Since the projection may be chosen freely, this allows for weighting dimensions to different degrees, etc.

--{-# ANN kmeansGen "n: Int -> f:(a -> {v:[Double] | len(v)=n}) -> k:Int -> points:[a] -> [[a]]" #-}
--kmeansGen :: Int -> (a -> [Double]) -> Int -> [a] -> [[a]]
--kmeansGen n f k points = kmeans' n k points
kmeansGen n f k points = map (map id) . kmeans' n k . map id $ points
--kmeansGen n f k points = map (map getVal) . kmeans' n k . map (\x -> WrapType (f x) x) $ points

--kmeansGen n f k points = map (map getVal) clusters
--  where wpoints  = map (\x -> WrapType (f x) x) points 
--        clusters = kmeans' n k wpoints 















