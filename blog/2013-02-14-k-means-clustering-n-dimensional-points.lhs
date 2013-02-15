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

\begin{code}
{-# LANGUAGE ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances #-}

module Data.KMeans (kmeans, kmeansGen) where

import Data.List (sort, span, minimumBy)
import Data.Function (on)
import Data.Ord (comparing)
import Language.Haskell.Liquid.Prelude (liquidAssert, liquidError)
\end{code}

Rather than reinvent the wheel, lets modify an existing implementation
of K-Means, [available on hackage](hackage-kmeans). This may not be the
most efficient implementation, but its a nice introduction to the algorithm, 
and the general invariants will hold for more sophisticated implementations.

The Game: Clustering Points
---------------------------

The goal of [K-Means clustering](http://en.wikipedia.org/wiki/K-means_clustering) 
is the following. Given as 

- **Input** : A set of *points* represented by *n-dimensional points* in *Euclidian* space

generate as

- **Ouptut** : A partitioning of the points, into K-clusters, 
  in a manner that minimizes sum of distances between the points 
  and their K-cluster centers.


The Players: Types
------------------

Lets make matters concrete by creating types that will represent the 
different elements of the algorithm.

1. **Fixed-Length Lists**  We will represent n-dimensional points using 
   good old Haskell lists, refined with a predicate that describes the
   dimensionality (i.e. length.) To simplify matters, lets package this 
   into a *type alias* that denotes lists of a given length `N` 

\begin{code}
{-@ type List a N = {v : [a] | (len v) = N} @-}
\end{code}

2. **Points** Next, we can represent an `N`-dimensional point as list of
   `Double` of length `N`, or in brief,

\begin{code}
{-@ type Point N = List Double N @-}
\end{code}

3. **Generalized Points** To be more flexible, we will support arbitrary
points as long as they can be **projected** to Euclidian space (which
allows for weighting dimensions to different degrees.) We encode
these points as

\begin{code}
{-@ type GenPoint a N  = WrapType (Point N) a @-} 
\end{code}

where `WrapType` is simply a Haskell record type

\begin{code}
data WrapType b a = WrapType {getVect :: b, getVal :: a}

instance Eq (WrapType [Double] a) where
   (==) = (==) `on` getVect

instance Ord (WrapType [Double] a) where
    compare = comparing getVect
\end{code}

4. **Clusters** Finally, a cluster is a *non-empty* list of points,

\begin{code}
{-@ type NEList a = {v : [a] | (len v) > 0} @-}
\end{code}

and a `Clustering` is a non-empty list of clusters.

\begin{code}
{-@ type Clustering a  = [(NEList a)] @-}
\end{code}


Warm-up: Basic Operations
-------------------------

Ok, with the types firmly in hand, let us go forth and develop the KMeans
clustering implementation. We will use a variety of small helper functions
(of the kind found in `Data.List`.) Lets get started by looking at them
through our new *refined* eyes.


Grouping
--------

The first such function is [groupBy][URL-groupBy]. We can
refine its type so that instead of just producing a `[[a]]` we know that it
produces a `Clustering a`, meaning a list of *non-empty* lists.

\begin{code}
{-@ groupBy       :: (a -> a -> Bool) -> [a] -> (Clustering a) @-}
groupBy _  []     =  []
groupBy eq (x:xs) =  (x:ys) : groupBy eq zs
  where (ys,zs)   = span (eq x) xs
\end{code}

Intuitively, its pretty easy to see how LiquidHaskell verifies the refined 
specification:

- Each element of the output list is of the form `x:ys` 
- For any list `ys` the length is non-negative, i.e. `(len ys) >= 0`
- The `len` of `x:ys` is `1 + (len ys)`, that is, strictly positive.

Partitioning
------------

HEREHEREHEREHERE

\begin{code}
{-@ partition           :: size:PosInt -> [a] -> (Clustering a) @-}
partition size []       = []
partition size ys@(_:_) = zs : part size zs' 
  where 
    zs                  = take size ys
    zs'                 = drop size ys
\end{code}


Zipping
-------

\begin{code}
{-@ safeZipWith :: (a -> b -> c) -> xs:[a] -> (List b (len xs)) -> (List c (len xs)) @-}
safeZipWith f (a:as) (b:bs) = f a b : safeZipWith f as bs
safeZipWith _ [] []         = []

-- Other cases only for exposition 
safeZipWith _ (_:_) []      = liquidError "safeZipWith1"
safeZipWith _ [] (_:_)      = liquidError "safeZipWith2"
\end{code}


Transposing
-----------

\begin{code}
{-@ type Matrix a N M        = List (List a N) M @-}

{-@ transpose                :: n:Int -> m:{v:Int| v > 0} -> Matrix a n m -> Matrix a m n @-}
transpose                    :: Int -> Int -> [[a]] -> [[a]]
transpose 0 _ _              = []
transpose n m ((x:xs) : xss) = (x : map head xss) : transpose (n - 1) m (xs : map tail xss)
-- transpose n m ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : transpose (xs : [ t | (_:t) <- xss])
transpose n m ([] : _)       = liquidError "transpose1" 
transpose n m []             = liquidError "transpose2"
\end{code}







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

{-@ clusterCenter      :: n:Int -> NEList (GenPoint a n) -> Point n @-}
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


[vecbounds]:    /blog/2013/01/05/bounding-vectors.lhs/ 
[ghclist]:      https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/GHC/List.lhs#L125
[foldl1]:       http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html#foldl1
[safeList]:     /blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/ 
[URL-groupBy]:  http://hackage.haskell.org/packages/archive/base/latest/doc/html/Data-List.html#v:groupBy


