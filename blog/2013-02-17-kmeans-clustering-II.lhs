---
layout: post
title: "KMeans Clustering: II"
date: 2013-02-17 16:12
author: Ranjit Jhala
published: false 
comments: true
external-url:
categories: basic measures 
demo: KMeans.hs
---

**The story so far:** [Previously][kmeansI] we saw

- how to encode `n`-dimensional points using plain old Haskell lists, 
- how to encode a matrix with `r` rows and `c` columns as a list of lists,
- some basic operations on points and matrices via list-manipulating functions

More importantly, we saw how easy it was to encode dimensionality with refinements over 
the `len` measure, thereby allowing LiquidHaskell to precisely track the dimensions across
the various operations. 

Next, lets use the basic types and operations to develop the actual *KMeans clustering* 
algorithm, and, along the way, see how LiquidHaskell lets us write precise module 
contracts which will ward against various unpleasant *lumpenexceptions*.

<!-- more -->

\begin{code}
{-# LANGUAGE ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances #-}

module KMeans (kmeans, kmeansGen) where

import KMeansHelper 

import Data.List (sort, span, minimumBy)
import Data.Function (on)
import Data.Ord (comparing)
import Language.Haskell.Liquid.Prelude (liquidAssert, liquidError)

instance Eq (WrapType [Double] a) where
   (==) = (==) `on` getVect

instance Ord (WrapType [Double] a) where
    compare = comparing getVect
\end{code}

Recall that we are using a modified version of an [existing KMeans implementation][URL-kmeans]. 
While not the swiftest implementation, it serves as a nice introduction to the algorithm, 
and the general invariants carry over to more sophisticated implementations.

A Quick Recap 
-------------

Before embarking on the journey, lets remind ourselves of our destination:
the goal of [K-Means clustering](http://en.wikipedia.org/wiki/K-means_clustering) is 

- **Take as Input** : A set of *points* represented by *n-dimensional points* in *Euclidian* space

- **Return as Ouptut** : A partitioning of the points, into upto K clusters, in a manner that 
  minimizes sum of distances between each point and its cluster center.

Last time, we introduced a variety of refinement type aliases for Haskell lists

\begin{code} Lists with a Fixed Length 
type List a N = {v : [a] | (len v) = N}
\end{code}

\begin{code} Non-empty Lists
type NonEmptyList a = {v : [a] | (len v) > 0} 
\end{code}

\begin{code} `N`-Dimensional Points
type Point N = List Double N
\end{code}

\begin{code} Matrices
type Matrix a Rows Cols = List (List a Cols) Rows
\end{code}

We also saw a bunch of list operations

- `groupBy`
- `partition`
- `safeZipWith` 
- `transpose`  

whose types will prove essential in order to verify the invariants of the 
clustering algorithm. You might open the [previous episode][kmeansI] in a
separate tab to keep those functions handy, but fear not!, we will refresh
our memory about them when we get around to using them below.

Generalized Points
------------------

To be more flexible, we will support *arbitrary* points as long as they can 
be **projected** to Euclidian space. In addition to supporting, say, an
image or a [cat video][maru], as a point, this will allow us to *weight*
different dimensions to different degrees.

We represent generalized points with a record

\begin{code}
data WrapType b a = WrapType {getVect :: b, getVal :: a}
\end{code}

and we can define an alias that captures the dimensionality of the point

\begin{code}
{-@ type GenPoint a N  = WrapType (Point N) a @-} 
\end{code}

That is, `GenPoint a N` denotes a general `a` value that has an
`N`-dimensional projection into Euclidean space.

Algorithm: Iterative Clustering
-------------------------------

\begin{code}
{-@ kmeans' :: n:Int -> k:PosInt -> [(GenPoint a n)] -> (Clustering (GenPoint a n)) @-}
kmeans' n k points = kmeansLoop n initialCluster
  where 
    initialCluster = partitition clusterSize points 
    clusterSize    = max 1 ((length points + k - 1) `div` k)

{-@ kmeansLoop :: n:Int -> (Clustering (GenPoint a n)) -> (Clustering (GenPoint a n)) @-}
kmeansLoop n clusters
  | clusters == clusters' = clusters
  | otherwise             = kmeansLoop n clusters'
  where clusters'         = reCluster n clusters
\end{code}

A Single-Step Of Reclustering
-----------------------------

\begin{code}
--------------------------------------------------------------------------------------------
-- One-Step of K-Means: Re-Cluster using current centers -----------------------------------
--------------------------------------------------------------------------------------------

{-@ reCluster          :: n:Int -> Clustering (GenPoint a n) -> Clustering (GenPoint a n) @-}
reCluster n clusters   = clusters' 
  where 
    -- 1. Compute cluster centers 
    centers            = map (clusterCenter n) clusters

    -- 2. Flatten clusters to get all points
    points             = concat clusters 
    
    -- 3. Map points to their nearest center
    centeredPoints     = sort [(nearestCenter n centers p, p) | p <- points]

    -- 4. Group points by nearest center
    centeredGroups     = groupBy ((==) `on` fst) centeredPoints 

    -- 5. Project groups back to the original points
    clusters'          = map (map snd) centeredGroups
\end{code}


Computing the Center of a Cluster
---------------------------------

`clusterCenter`

\begin{code}
--------------------------------------------------------------------------------------------
-- Determine the Center of a Cluster of Points ---------------------------------------------
--------------------------------------------------------------------------------------------

{-@ clusterCenter      :: n:Int -> NonEmptyList (GenPoint a n) -> Point n @-}
clusterCenter n points = map ((`safeDiv` numPoints) . sum) points'  -- divide By Zero
  where 
    numPoints          = length points 
    points'            = transpose n numPoints (map getVect points)
\end{code}


\begin{code}
{- safeDiv   :: (Fractional a) => a -> {v:Int | v != 0} -> a -}
safeDiv n 0   = liquidError "divide by zero"
safeDiv n d   = n / (fromIntegral d)
\end{code}

Finding the Nearest Center
--------------------------

`nearestCenter` 

\begin{code}
--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------

{-@ nearestCenter         :: n:Int -> [(Point n)] -> (GenPoint a n) -> (Point n)  @-} 
nearestCenter n centers p = minKey centerDistances 
  where 
    centerDistances       = [(ci, distance ci (getVect p)) | ci <- centers] 
    
    minimumKey            :: (Ord v) => [(k, v)] -> k
    minimumKey kvs        = minimumBy (\x y -> compare (snd x) (snd y)) kvs

    distance              ::  [Double] -> [Double] -> Double 
    distance a b          = sqrt . sum $ safeZipWith (\x y -> (x-y)^2) a b      -- safeZipWith dimensions
\end{code}


Putting It All Together: Top-Level API
--------------------------------------

Use types to explain top-level

\begin{code}
--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------

-- | A generalized kmeans function. This function operates not on points, but an arbitrary type 
--   which may be projected into a Euclidian space. Since the projection may be chosen freely, 
--   this allows for weighting dimensions to different degrees, etc.

{-@ kmeansGen :: n:Int -> (a -> (Point n)) -> k:PosInt -> points:[a] -> (Clustering a) @-}
kmeansGen :: Int -> (a -> [Double]) -> Int -> [a] -> [[a]]
kmeansGen n project k = map (map getVal) 
                      . kmeans' n k 
                      . map (\x -> WrapType (project x) x) 

-- | A specialized kmeans function, that operates on points in n-dimensional Euclidian space, 
--   where the points are represented as [Double] of length n. Implemented using the general 
--   `kmeansGen` via the trivial `id` projection.

{-@ kmeans :: n:Int -> k:PosInt -> points:[(Point n)] -> (Clustering (Point n)) @-}
kmeans     :: Int -> Int -> [[Double]] -> [[[Double]]]
kmeans n   = kmeansGen n id
\end{code}

Conclusions
-----------

1. How to do *K-Means Clustering* !

2. Track precise length properties with **measures**

3. Circumvent limitations of SMT with a touch of **dynamic** checking using **assumes**

[safeList]:      /blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/ 
[kmeansI]:       /blog/2013/02/16/kmeans-clustering-I.lhs/
[kmeansII]:      /blog/2013/02/17/kmeans-clustering-II.lhs/
[URL-take]:      https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/GHC/List.lhs#L334
[URL-groupBy]:   http://hackage.haskell.org/packages/archive/base/latest/doc/html/Data-List.html#v:groupBy
[URL-transpose]: http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html#transpose
[maru]:          http://www.youtube.com/watch?v=8uDuls5TyNE
[demo]:          http://goto.ucsd.edu/~rjhala/liquid/haskell/demo/#?demo=KMeansHelper.hs
[URL-kmeans]:    http://hackage.haskell.org/package/kmeans


