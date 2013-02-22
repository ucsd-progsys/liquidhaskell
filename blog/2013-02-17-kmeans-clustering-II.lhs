---
layout: post
title: "KMeans Clustering II"
date: 2013-02-17 16:12
author: Ranjit Jhala
published: true
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
import Prelude              hiding      (zipWith)
import Data.List                        (sort, span, minimumBy)
import Data.Function                    (on)
import Data.Ord                         (comparing)
import Language.Haskell.Liquid.Prelude  (liquidAssert, liquidError)

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
  minimizes the sum of distances between each point and its cluster center.

Last time, we introduced a variety of refinement type aliases for Haskell lists

\begin{code} **Fixed Length Lists**
type List a N = {v : [a] | (len v) = N}
\end{code}

\begin{code} **Non-empty Lists**
type NonEmptyList a = {v : [a] | (len v) > 0}
\end{code}

\begin{code} **N-Dimensional Points**
type Point N = List Double N
\end{code}

\begin{code} **Matrices**
type Matrix a Rows Cols = List (List a Cols) Rows
\end{code}

\begin{code} We also saw several basic list operations
groupBy   :: (a -> a -> Bool) -> [a] -> (Clustering a)
partition :: PosInt -> [a] -> (Clustering a)
zipWith   :: (a -> b -> c) -> xs:[a] -> (List b (len xs)) -> (List c (len xs))
transpose :: c:Int -> r:PosInt -> Matrix a r c -> Matrix a c r
\end{code}

whose types will prove essential in order to verify the invariants of the
clustering algorithm. You might open the [previous episode][kmeansI] in a
separate tab to keep those functions handy, but fear not, we will refresh
our memory about them when we get around to using them below.

Generalized Points
------------------

To be more flexible, we will support *arbitrary* points as long as they can
be **projected** to Euclidian space. In addition to supporting, say, an
image or a [cat video][maru] as a point, this will allow us to *weight*
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

Terrific, now that all the pieces are in place lets look at the KMeans
algorithm. We have implemented a function `kmeans'`, which takes as input a
dimension `n`, the maximum number of clusters `k` (which must be positive),
a list of *generalized points* of dimension `n`, and returns a `Clustering`
(i.e. a list of *non-empty lists*) of the generalized points.

So much verbiage -- a type is worth a thousand comments!

\begin{code}
{-@ kmeans' :: n:Int
            -> k:PosInt
            -> points:[(GenPoint a n)]
            -> (Clustering (GenPoint a n)) @-}
\end{code}

There! Crisp and to the point. Sorry. Anyhoo, the function implements the
above type.

\begin{code}
kmeans' n k points    = fixpoint (refineCluster n) initialClustering
  where
    initialClustering = partition clusterSize points
    clusterSize       = max 1 ((length points + k - 1) `div` k)

    fixpoint          :: (Eq a) => (a -> a) -> a -> a
    fixpoint f x      = if (f x) == x then x else fixpoint f (f x)
\end{code}

That is, `kmeans'` creates an `initialClustering` by
`partition`-ing the `points` into chunks with `clusterSize` elements.
Then, it invokes `fixpoint` to *iteratively refine* the initial
clustering  with `refineCluster` until it converges to a stable
clustering that cannot be improved upon. This stable clustering
is returned as the output.

LiquidHaskell verifies that `kmeans'` adheres to the given signature in two steps.

**1. Initial Clustering**

\begin{code} First, LiquidHaskell determines from
max       :: (Ord a) => x:a -> y:a -> {v: a | (v >= x) && ( v >= y) }
\end{code}

\begin{code} that `clusterSize` is strictly positive, and hence, from
partition :: size:PosInt -> [a] -> (Clustering a)
\end{code}

which we saw [last time][kmeansI], that `initialClustering` is indeed
a valid `Clustering` of `(GenPoint a n)`.

**2. Fixpoint**

Next, LiquidHaskell infers that at the call `fixpoint (refineCluster n)
...`, that the type parameter `a` of `fixpoint` can be *instantiated* with
`Clustering (GenPoint a n)`.  This is because `initialClustering` is a
valid clustering, as we saw above, and because `refineCluster` takes -- and
returns -- valid `n`-dimensional clusterings, as we shall see below.
Consequently, the value returned by `kmeans'` is also `Clustering` of
`GenPoint a n` as required.

Refining A Clustering
---------------------

Thus, the real work in KMeans happens inside `refineCluster`, which takes a
clustering and improves it, like so:

\begin{code}
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
\end{code}

The behavior of `refineCluster` is pithily captured by its type

\begin{code}
{-@ refineCluster :: n:Int
                  -> Clustering (GenPoint a n)
                  -> Clustering (GenPoint a n) @-}
\end{code}

The refined clustering is computed in three steps.

1. First, we compute the `centers :: [(Point n)]` of the current `clusters`.
   This is achieved by using `clusterCenter`, which maps a list of generalized
   `n`-dimensional points to a *single* `n` dimensional point (i.e. `Point n`).

2. Next, we pair each point `p` in the list of all `points` with its `nearestCenter`.

3. Finally, the pairs in the list of `centeredPoints` are grouped by the
   center, i.e. the first element of the tuple. The resulting groups are
   projected back to the original generalized points yielding the new
   clustering.

\begin{code} The type of the output follows directly from
groupBy :: (a -> a -> Bool) -> [a] -> (Clustering a)
\end{code}

from [last time][kmeansI]. At the call site above, LiquidHaskell infers that
`a` can be instantiated with `((Point n), (GenPoint a n))` thereby establishing
that, after *projecting away* the first element, the output is a list of
non-empty lists of generalized `n`-dimensional points.

That leaves us with the two crucial bits of the algorithm: `clusterCenter`
and `nearestCenter`.

Computing the Center of a Cluster
---------------------------------

The center of an `n`-dimensional cluster is simply an `n`-dimensional point
whose value in each dimension is equal to the *average* value of that
dimension across all the points in the cluster.

\begin{code} For example, consider a cluster of 2-dimensional points,
exampleCluster = [ [0,  0]
                 , [1, 10]
                 , [2, 20]
                 , [4, 40]
                 , [5, 50] ]
\end{code}

\begin{code} The center of the cluster is
exampleCenter = [ (0 + 1  + 2  + 4  + 5 ) / 5
                , (0 + 10 + 20 + 40 + 50) / 5 ]
\end{code}

\begin{code} which is just
exampleCenter = [ 3, 30 ]
\end{code}

Thus, we can compute a `clusterCenter` via the following procedure

\begin{code}
clusterCenter n xs = map average xs'
  where
    numPoints      = length xs
    xs'            = transpose n numPoints (map getVect xs)

    average        :: [Double] -> Double
    average        = (`safeDiv` numPoints) . sum
\end{code}

First, we `transpose` the matrix of points in the cluster.
Suppose that `xs` is the `exampleCluster` from above
(and so `n` is `2` and `numPoints` is `5`.)

\begin{code} In this scenario, `xs'` is
xs' = [ [0,  1,  2,  4,  5]
      , [0, 10, 20, 40, 50] ]
\end{code}

and so `map average xs'` evaluates to `exampleCenter` from above.

We have ensured that the division in the average does not lead to
any nasty surprises via a *safe division* function whose precondition
checks that the denominator is non-zero, [as illustrated here][ref101].

\begin{code}
{- safeDiv   :: (Fractional a) => a -> {v:Int | v != 0} -> a -}
safeDiv     :: (Fractional a) => a -> Int -> a
safeDiv n 0 = liquidError "divide by zero"
safeDiv n d = n / (fromIntegral d)
\end{code}

LiquidHaskell verifies that the divide-by-zero never occurs, and furthermore,
that `clusterCenter` indeed computes an `n`-dimensional center by inferring that

\begin{code}
{-@ clusterCenter :: n:Int -> NonEmptyList (GenPoint a n) -> Point n @-}
\end{code}

LiquidHaskell deduces that the *input* list of points `xs` is non-empty
from the fact that `clusterCenter` is only invoked on the elements of a
`Clustering` which comprise only non-empty lists. Since `xs` is non-empty,
i.e. `(len xs) > 0`, LiquidHaskell infers that `numPoints` is positive
(hover over `length` to understand why), and hence, LiquidHaskell is
satisfied that the call to `safeDiv` will always proceed without any
incident.

\begin{code} To establish the *output* type `Point n` LiquidHaskell leans on the fact that
transpose :: n:Int -> m:PosInt -> Matrix a m n -> Matrix a n m
\end{code}

to deduce that `xs'` is of type `Matrix Double n numPoints`, that is to
say, a list of length `n` containing lists of length `numPoints`. Since
`map` preserves the length, the value `map average xs'` is also a list
of length `n`, i.e. `Point n`.


Finding the Nearest Center
--------------------------

The last piece of the puzzle is `nearestCenter` which maps each
(generalized) point to the center that it is nearest. The code is
pretty self-explanatory:

\begin{code}
nearestCenter     :: Int -> WrapType [Double] a -> [[Double]] -> [Double]
nearestCenter n x = minKey . map (\c -> (c, distance c (getVect x)))
\end{code}

We `map` the centers to a tuple of center `c` and the `distance` between
`x` and `c`, and then we select the tuple with the smallest distance

\begin{code}
minKey  :: (Ord v) => [(k, v)] -> k
minKey  = fst . minimumBy (\x y -> compare (snd x) (snd y))
\end{code}

The interesting bit is that the `distance` function uses `zipWith` to
ensure that the dimensionality of the center and the point match up.

\begin{code}
distance     :: [Double] -> [Double] -> Double
distance a b = sqrt . sum $ zipWith (\v1 v2 -> (v1 - v2) ^ 2) a b
\end{code}

LiquidHaskell verifies `distance` by inferring that

\begin{code}
{-@ nearestCenter :: n:Int -> (GenPoint a n) -> [(Point n)] -> (Point n) @-}
\end{code}

First, LiquidHaskell deduces that each center in `cs` is indeed `n`-dimensional, which
follows from the output type of `clusterCenter`. Since `x` is a `(GenPoint a n)`
LiquidHaskell infers that both `c` and `getVect x` are of an equal length `n`.

\begin{code} Consequently, the call to
zipWith :: (a -> b -> c) -> xs:[a] -> (List b (len xs)) -> (List c (len xs))
\end{code}

[discussed last time][kmeansI] is determined to be safe.

Finally, the value returned is just one of the input centers and so is a `(Point n)`.


Putting It All Together: Top-Level API
--------------------------------------

We can bundle the algorithm into two top-level API functions.

First, a version that clusters *generalized* points. In this case, we
require a function that can `project` an `a` value to an `n`-dimensional
point. This function just wraps each `a`, clusters via `kmeans'` and then
unwraps the points.

\begin{code}
{-@ kmeansGen :: n:Int
              -> (a -> (Point n))
              -> k:PosInt
              -> xs:[a]
              -> (Clustering a)
  @-}

kmeansGen n project k = map (map getVal)
                      . kmeans' n k
                      . map (\x -> WrapType (project x) x)
\end{code}

Second, a specialized version that operates directly on `n`-dimensional
points. The specialized version just calls the general version with a
trivial `id` projection.

\begin{code}
{-@ kmeans :: n:Int
           -> k:PosInt
           -> points:[(Point n)]
           -> (Clustering (Point n))
  @-}

kmeans n   = kmeansGen n id
\end{code}

Conclusions
-----------

I hope that over the last two posts you have gotten a sense of

1. What KMeans clustering is all about,

2. How measures and refinements can be used to describe the behavior
   of common list operations like `map`, `transpose`, `groupBy`, `zipWith`, and so on,

3. How LiquidHaskell's automated inference makes it easy to write and
   verify invariants of non-trivial programs.

The sharp reader will have noticed that the one *major*, non syntactic, change to the
[original code][URL-kmeans] is the addition of the dimension parameter `n` throughout
the code. This is critically required so that we can specify the relevant
invariants (which are in terms of `n`.) The value is actually a ghost, and
never ever used. Fortunately, Haskell's laziness means that we don't have
to worry about it (or other ghost variables) imposing any run-time overhead
at all.

**Exercise:** Incidentally, if you have followed thus far I would
encourage you to ponder about how you might modify the types (and
implementation) to verify that KMeans indeed produces at most `k` clusters...

[ref101]:        /blog/2013/01/01/refinement-types-101.lhs/
[safeList]:      /blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/
[kmeansI]:       /blog/2013/02/16/kmeans-clustering-I.lhs/
[kmeansII]:      /blog/2013/02/17/kmeans-clustering-II.lhs/
[URL-take]:      https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/GHC/List.lhs#L334
[URL-groupBy]:   http://hackage.haskell.org/packages/archive/base/latest/doc/html/Data-List.html#v:groupBy
[URL-transpose]: http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html#transpose
[maru]:          http://www.youtube.com/watch?v=8uDuls5TyNE
[demo]:          http://goto.ucsd.edu/~rjhala/liquid/haskell/demo/#?demo=KMeansHelper.hs
[URL-kmeans]:    http://hackage.haskell.org/package/kmeans


