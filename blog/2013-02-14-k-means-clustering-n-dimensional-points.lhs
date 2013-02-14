---
layout: post
title: "KMeans Clustering N-Dimensional Points"
date: 2013-02-14 16:12
author: Ranjit Jhala
published: false 
comments: true
external-url:
categories: basic measures 
demo: kmeans.hs
---

[Last time][safeList] we introduced a new specification called a *measure*
and demonstrated how to use it to encode the *length* of a list, and
thereby verify that functions like `head` and `tail` were only called with
non-empty lists (whose length was *strictly* greater than `0`.) As several
folks pointed out, once LiquidHaskell can reason about lengths, it can do a
lot more than just analyze non-emptiness. 

Indeed! 

So today, let me show you how one might implement a k-means algorithm that
clusters `n`-dimensional points into at most k groups, and how
LiquidHaskell can help us write and enforce these size requirements. 

<!-- For example, XXX pointed out that we can use the type
system to give an *upper* bound on the size of a list, e.g. 
using lists upper bounded by a gigantic `MAX_INT` value as
a proxy for finite lists.
-->

<!-- more -->

Rather than reinvent the wheel, lets start with an existing implementation
of K-Means, available [on hackage](hackage-kmeans). This may not be the most 
efficient implementation, but its a nice introduction to the algorithm, and
the general invariants will hold for more sophisticated implementations.

\begin{code}
{-# LANGUAGE ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances #-}

module Data.KMeans (kmeans, kmeansGen) where

import Data.List (sort, span, minimumBy)
import Data.Function (on)
import Data.Ord (comparing)
import Language.Haskell.Liquid.Prelude (liquidAssert, liquidError)

{-@ type NNList a     = { v : [a] | (len v) > 0 } @-}
{-@ type List a N     = { v : [a] | (len v) = N } @-}
{-@ type Matrix a N M = List (List a N) M         @-}
{-@ type Point N      = List Double N             @-}
{-@ type Clustering a = [(NNList a)]              @-}

-- TODO: define CLUSTER type

---------------------------------------------------------------------------------------------------

data WrapType b a = WrapType {getVect :: b, getVal :: a}

instance Eq (WrapType [Double] a) where
   (==) = (==) `on` getVect

instance Ord (WrapType [Double] a) where
    compare = comparing getVect

--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------

-- TODO: SHOW TYPE
clusterCenter n points = map ((`safeDiv` numPoints) . sum) points'  -- divide By Zero
  where 
    numPoints          = length points 
    points'            = transpose n m (map getVect points)

-- HOIST
{-@ safeDiv   :: (Fractional a) => a -> {v:Int | v != 0} -> a @-}
safeDiv n 0   = liquidError "divide by zero"
safeDiv n d   = n / (fromIntegral d)

-- HOIST
{-@ transpose                :: n:Int -> m:{v:Int| v > 0} -> Matrix a n m -> Matrix a m n @-}
transpose                    :: Int -> Int -> [[a]] -> [[a]]
transpose 0 _ _              = []
transpose n m ((x:xs) : xss) = (x : map head xss) : transpose (n - 1) m (xs : map tail xss)
-- transpose n m ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : transpose (xs : [ t | (_:t) <- xss])
transpose n m ([] : _)       = liquidError "transpose1" 
transpose n m []             = liquidError "transpose2"

--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------

-- TODO: SHOW TYPE
recluster n clusters   = clusters' 
  where 
    points             = concat clusters 
    centers            = map (clusterCenter n) clusters
    centeredPoints     = sort $ map (nearestCenter n centers) points
    centeredGroups     = groupBy ((==) `on` fst) centeredPoints 
    clusters'          = map (map snd) centeredGroups

-- HOIST
{-@ groupBy       :: (a -> a -> Bool) -> [a] -> (Clustering a) @-}
groupBy _  []     =  []
groupBy eq (x:xs) =  (x:ys) : groupBy eq zs
                     where (ys,zs) = span (eq x) xs

--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------

-- TODO: SHOW TYPE
nearestCenter n ctrs p = (minKey centerDistances, p) 
  where 
    centerDistances    = [(ci, distance ci (getVect p)) | ci <- ctrs] 

distance     ::  [Double] -> [Double] -> Double 
distance a b = sqrt . sum $ safeZipWith (\x y -> (x-y)^2) a b      -- safeZipWith dimensions

-- HOIST
{-@ safeZipWith :: (a -> b -> c) -> xs:[a] -> (List b (len xs)) -> (List c (len xs)) @-}

safeZipWith f (a:as) (b:bs) = f a b : safeZipWith f as bs
safeZipWith _ [] []         = []
safeZipWith _ (_:_) []      = liquidError "safeZipWith1"
safeZipWith _ [] (_:_)      = liquidError "safeZipWith2"

minKey       :: (Ord v) => [(k, v)] -> k
minKey kvs   = minimumBy (\x y -> compare (snd x) (snd y)) kvs

--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------

kmeans' n k points = kmeansLoop n initialCluster
  where 
    initialCluster = part clusterSize points 
    clusterSize    = max 1 ((length points + k - 1) `div` k)

-- TODO: SHOW TYPE
kmeansLoop n clusters
  | clusters == clusters' = clusters
  | otherwise             = kmeansLoop n clusters'
  where clusters'         = recluster n clusters

-- HOIST
{-@ part        :: n:{v:Int | v > 0} -> [a] -> (Clustering a) @-}
part n []       = []
part n ys@(_:_) = zs : part n zs' 
  where zs      = take n ys
        zs'     = drop n ys

--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------


-- | Cluster points in a Euclidian space, represented as lists of Doubles, into at most k clusters.
-- The initial clusters are chosen arbitrarily.
{-@ kmeans :: n:Int -> k:Int -> points:[(List Double n)] -> [[(List Double n)]] @-}
kmeans :: Int -> Int -> [[Double]] -> [[[Double]]]
kmeans n = kmeansGen n id

-- | A generalized kmeans function. This function operates not on points, but an arbitrary type 
--   which may be projected into a Euclidian space. Since the projection may be chosen freely, 
-- this allows for weighting dimensions to different degrees, etc.

{-@ kmeansGen :: n: Int -> f:(a -> (List Double n)) -> k:Int -> points:[a] -> [[a]] @-}
kmeansGen :: Int -> (a -> [Double]) -> Int -> [a] -> [[a]]
kmeansGen n f k points = map (map getVal) . kmeans' n k . map (\x -> WrapType (f x) x) $ points


\end{code}



Conclusions
-----------

1. How to do *K-Means Clustering* !

2. Track precise length properties with **measures**

3. Circumvent limitations of SMT with a touch of **dynamic** checking using **assumes**


[vecbounds]:  /blog/2013/01/05/bounding-vectors.lhs/ 
[ghclist]:    https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/GHC/List.lhs#L125
[foldl1]:     http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html#foldl1
[safeList]:   /blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/ 



