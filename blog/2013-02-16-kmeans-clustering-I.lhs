---
layout: post
title: "KMeans Clustering: I"
date: 2013-02-14 16:12
author: Ranjit Jhala
published: false 
comments: true
external-url:
categories: basic measures 
demo: KMeans1.hs
---

[Last time][safeList] we introduced a new specification called a *measure*
and demonstrated how to use it to encode the *length* of a list, and thereby
verify that functions like `head` and `tail` were only called with non-empty 
lists (whose length was *strictly* greater than `0`.) As several folks pointed
out, once LiquidHaskell can reason about lengths, it can do a lot more than just
analyze non-emptiness. 

Indeed! 

Over the *next two posts*, let me show you how one might implement a
Kmeans algorithm that clusters `n`-dimensional points groups, and how
LiquidHaskell can help us write and enforce various dimensionality
invariants along the way. 

<!-- more -->


<!-- For example, XXX pointed out that we can use the type
system to give an *upper* bound on the size of a list, e.g. 
using lists upper bounded by a gigantic `MAX_INT` value as
a proxy for finite lists.
-->


\begin{code}
{-# LANGUAGE ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances #-}

module KMeans1 where

import Data.List (sort, span, minimumBy)
import Data.Function (on)
import Data.Ord (comparing)
import Language.Haskell.Liquid.Prelude (liquidAssert, liquidError)
\end{code}

Rather than reinvent the wheel, we will modify an existing implementation
of K-Means, [available on hackage](hackage-kmeans). This may not be the
most efficient implementation, but its a nice introduction to the algorithm, 
and the general invariants will hold for more sophisticated implementations.

We have broken this entry into two convenient, bite-sized chunks:

+ **Part I**  Introduces the basic types and list operations needed by KMeans,
+ **Part II** Describes how the operations are used in the KMeans implementation.


The Game: Clustering Points
---------------------------

The goal of [K-Means clustering](http://en.wikipedia.org/wiki/K-means_clustering) 
is the following. Given as 

- **Input** : A set of *points* represented by *n-dimensional points* 
  in *Euclidian* space

generate as

- **Ouptut** : A partitioning of the points, into K clusters, in a manner that 
  minimizes sum of distances between each point and its cluster center.


The Players: Types
------------------

Lets make matters concrete by creating types that will represent the 
different elements of the algorithm.

1. **Fixed-Length Lists**  We will represent n-dimensional points using 
   good old Haskell lists, refined with a predicate that describes the
   dimensionality (i.e. length.) To simplify matters, lets package this 
   into a *type alias* that denotes lists of a given length `N`. 
   
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

where `WrapType` is just a Haskell record type

\begin{code}
data WrapType b a = WrapType {getVect :: b, getVal :: a}

instance Eq (WrapType [Double] a) where
   (==) = (==) `on` getVect

instance Ord (WrapType [Double] a) where
    compare = comparing getVect
\end{code}

4. **Clusters** Finally, a cluster is a **non-empty** list of points,

\begin{code}
{-@ type NEList a = {v : [a] | (len v) > 0} @-}
\end{code}

and a `Clustering` is a non-empty list of clusters.

\begin{code}
{-@ type Clustering a  = [(NEList a)] @-}
\end{code}

**Note:** When defining refinement type aliases, we use uppercase variables 
like `N`  to distinguish value- parameters from the lowercase type parameters 
like `a`.

Basic Operations
----------------

Ok, with the types firmly in hand, let us go forth and develop the KMeans
clustering implementation. We will use a variety of small helper functions
(of the kind found in `Data.List`.) Lets get started by looking at them
through our new *refined* eyes.


**Grouping**

The first such function is [groupBy][URL-groupBy]. We can
refine its type so that instead of just producing a `[[a]]` 
we know that it produces a `Clustering a` which is a list 
of *non-empty* lists.

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

**Partitioning**

Next, lets look the function

\begin{code}
{-@ partition           :: size:PosInt -> [a] -> (Clustering a) @-}
\end{code}

which is given a *strictly positive* integer argument, that is,

\begin{code}
{-@ type PosInt = {v: Int | v > 0 } @-}
\end{code}

and a list of `a` values, and which returns a `Clustering a`, 
that is, a list of non-empty lists. (Each inner list has a length
that is less than `size` but we shall elide this for simplicity.)

The function is implemented in a straightforward manner, using the 
library functions `take` and `drop`

\begin{code}
partition size []       = []
partition size ys@(_:_) = zs : part size zs' 
  where 
    zs                  = take size ys
    zs'                 = drop size ys
\end{code}

To verify that a valid `Clustering` is produced, LiquidHaskell needs only
verify that the list `zs` above is non-empty, by suitably connecting the
properties of the inputs `size` and `ys` with the output. 

\begin{code} We have [previously verified][url-take] that
take :: n:{v: Int | v >= 0 } 
     -> xs:[a] 
     -> {v:[a] | (len v) = (if ((len xs) < n) then (len xs) else n) } 
\end{code}

In other words, the output list's length is the *smaller of* the input
list's length and `n`.  Thus, since both `size` and the `(len ys)` are
greater than `1`, LiquidHaskell deduces that the list returned by `take
size ys` has a length greater than `1`, i.e., is non-empty.

Zipping
-------

To compute the *Euclidean distance* between two points, we will use 
the `zipWith` function. To make sure that it is invoked on points 
with *the same number of dimensions*. To this end, we write a 

\begin{code}
{-@ safeZipWith :: (a -> b -> c) 
                -> xs:[a] 
                -> (List b (len xs)) 
                -> (List c (len xs)) 
  @-}

safeZipWith f (a:as) (b:bs) = f a b : safeZipWith f as bs
safeZipWith _ [] []         = []

-- Other cases only for exposition 
safeZipWith _ (_:_) []      = liquidError "Dead Code"
safeZipWith _ [] (_:_)      = liquidError "Dead Code"
\end{code}

The type stipulates that the second input list and the output have
the same length as the first input. Furthermore, it rules out the 
case where one list is empty and the other is not, as in that case, 
the former's length is zero while the latter's is not.

Transposing
-----------

The last basic operation that we will require, is a means to
*transpose* a `Matrix`, which itself is just a list of lists:

\begin{code}
{-@ type Matrix a Cols Rows = List (List a Cols) Rows @-}
\end{code}

The `transpose` operation flips the rows and columns

\begin{code}
{-@ transpose :: cols:Int 
              -> rows:PosInt 
              -> Matrix a cols rows 
              -> Matrix a rows cols 
  @-}
\end{code}

I confess can never really understand matrices without concrete examples!

So, lets say you have a matrix

~~~~~{.haskell}
m1  :: Matrix Int 2 4
m1  =  [ [1, 2]
       , [3, 4]
       , [5, 6] 
       , [7, 8] ]
~~~~~

then the matrix `m2 = transpose 2 3 m1` should be

~~~~~{.haskell}
m2 :: Matrix Int 4 2
m1  =  [ [1, 3, 5, 7]
       , [2, 4, 6, 8] ]
~~~~~

As you can work out from the above, the code for `transpose` is quite
straightforward: each *output row* is simply the list of `head`s of 
the *input rows*:


\begin{code}
transpose                    :: Int -> Int -> [[a]] -> [[a]]
transpose 0 _ _              = []
transpose n m ((x:xs) : xss) = (x : map head xss) : transpose (n - 1) m (xs : map tail xss)
-- transpose n m ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : transpose (xs : [ t | (_:t) <- xss])
transpose n m ([] : _)       = liquidError "dead code" 
transpose n m []             = liquidError "dead code"
\end{code}

By the way, the code above is essentially that of `Data.List.transpose`
[from the prelude][url-transpose] except that we have added dimension
parameters, used them to ensure that all rows have the same length, and
to precisely characterize the shape of the input and output lists.

We will use a `Matrix a n m` will denote a *single cluster* 
of `m` points each of which has `n` dimensions. We will 
transpose the matrix to make it easy to *sum* the points 
along *each* dimension, and thereby compute the *centroid* 
of the cluster.

Intermission
------------

Time for a break -- [go see a cat video!](http://www.youtube.com/watch?v=8uDuls5TyNE) -- or not! 
In the next installment, we'll use the types and functions described above,
to develop the clustering algorithm.

Part II: KMeans By Iterative Clustering
=======================================

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


[vecbounds]:     /blog/2013/01/05/bounding-vectors.lhs/ 
[ghclist]:       https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/GHC/List.lhs#L125
[foldl1]:        http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html#foldl1
[safeList]:      /blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/ 
[URL-groupBy]:   http://hackage.haskell.org/packages/archive/base/latest/doc/html/Data-List.html#v:groupBy
[url-transpose]: http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html#transpose
[url-take]:      https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/GHC/List.lhs#L334
