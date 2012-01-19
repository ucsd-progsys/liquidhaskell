{- |
Module      :  Data.KMeans
Copyright   :  (c) Keegan Carruthers-Smith, 2009
License     :  BSD 3 Clause
Maintainer  :  gershomb@gmail.com
Stability   :  experimental

A simple implementation of the standard k-means clustering algorithm: <http://en.wikipedia.org/wiki/K-means_clustering>. K-means clustering partitions points into clusters, with each point belonging to the cluster with th nearest mean. As the general problem is NP hard, the standard algorithm, which is relatively rapid, is heuristic and not guaranteed to converge to a global optimum. Varying the input order, from which the initial clusters are generated, can yield different results. For degenerate and malicious cases, the algorithm may take exponential time.

-}

{-# LANGUAGE ScopedTypeVariables #-}

module Data.KMeans (kmeans, kmeansGen)
    where

import Data.List (transpose, sort, groupBy, minimumBy)
import Data.Function (on)
import Data.Ord (comparing)

data WrapType a = WrapType {getVect :: [Double], getVal :: a}

instance Eq (WrapType a) where
   (==) = (==) `on` getVect

instance Ord (WrapType a) where
    compare = comparing getVect

dist a b = sqrt . sum $ zipWith (\x y-> (x-y) ^ 2) a b

centroid points = map (flip (/) l . sum) $ transpose (map getVect points)
    where l = fromIntegral $ length points

closest (n :: Int) points point = minimumBy (comparing $ dist point) points

recluster' n centroids points = map (map snd) $ groupBy ((==) `on` fst) reclustered
    where reclustered = sort [(closest n centroids (getVect a), a) | a <- points]

recluster n clusters = recluster' n centroids $ concat clusters
    where centroids = map centroid clusters

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

kmeans' n k points = kmeans'' n $ part l points
    where l = (length points + k - 1) `div` k

-- | Cluster points in a Euclidian space, represented as lists of Doubles, into at most k clusters.
-- The initial clusters are chosen arbitrarily.

{-# ANN kmeans "n: Int -> k:Int -> points:[{v:[Double] | len(v) = n}] -> [[{ v: [Double] | len(v) = n}]]" #-}
kmeans :: Int -> Int -> [[Double]] -> [[[Double]]]
kmeans n = kmeansGen n id

-- | A generalized kmeans function. This function operates not on points, but an arbitrary type which may be projected into a Euclidian space. Since the projection may be chosen freely, this allows for weighting dimensions to different degrees, etc.

{-# ANN kmeansGen "n: Int -> f:(a -> {v:[Double] | len(v)=n}) -> k:Int -> points:[a] -> [[a]]" #-}
kmeansGen :: Int -> (a -> [Double]) -> Int -> [a] -> [[a]]
kmeansGen n f k points = map (map getVal) . kmeans' n k . map (\x -> WrapType (f x) x) $ points














