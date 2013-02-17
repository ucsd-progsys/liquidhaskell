---
layout: post
title: "KMeans Clustering: I"
date: 2013-02-16 16:12
author: Ranjit Jhala
published: false 
comments: true
external-url:
categories: basic measures 
demo: KMeansHelper.hs
---

[Last time][safeList] we introduced a new specification mechanism called a 
*measure* and demonstrated how to use it to encode the *length* of a list. 
We saw how measure's could be used to verify that functions like `head` and 
`tail` were only called with non-empty lists (whose length was *strictly* 
greater than `0`.) As several folks pointed out, once LiquidHaskell can 
reason about lengths, it can do a lot more than just analyze non-emptiness. 

Indeed! 

Over the *next two posts*, let me show you how one might implement a
Kmeans algorithm that clusters `n`-dimensional points groups, and how
LiquidHaskell can help us write and enforce various dimensionality
invariants along the way. 

<!-- more -->

<!-- For example, XXX pointed out that we can use the type system to give an *upper* bound on the size of a list, e.g. using lists 
     upper bounded by a gigantic `MAX_INT` value as a proxy for finite lists. -->


\begin{code}
{-# LANGUAGE ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances #-}

module KMeansHelper where

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

3. **Clusters** Finally, A cluster is a **non-empty** list of points,

\begin{code}
{-@ type NonEmptyList a = {v : [a] | (len v) > 0} @-}
\end{code}

and a `Clustering` is a non-empty list of clusters.

\begin{code}
{-@ type Clustering a  = [(NonEmptyList a)] @-}
\end{code}

**Note:** When defining refinement type aliases, we use uppercase variables 
like `N`  to distinguish value- parameters from the lowercase type parameters 
like `a`.

**Note:** If you are familiar with the *index-style* length 
encoding e.g. as found in [DML][dml] or [Agda][agdavec], then mark 
that despite appearances, our `List` and `Point` definitions are 
*not indexed*, but just abbreviations. We deliberately choose to 
encode properties with logical refinement predicates, to facilitate 
SMT based checking and inference.


Ok, with the types firmly in hand, let us go forth and develop the KMeans
clustering implementation. We will use a variety of small helper functions
(of the kind found in `Data.List`.) Lets get started by looking at them
through our new *refined* eyes.

Grouping
--------

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

Partitioning
------------

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
partition size ys@(_:_) = zs : partition size zs' 
  where 
    zs                  = take size ys
    zs'                 = drop size ys
\end{code}

To verify that a valid `Clustering` is produced, LiquidHaskell needs only
verify that the list `zs` above is non-empty, by suitably connecting the
properties of the inputs `size` and `ys` with the output. 

\begin{code} We have [previously verified][URL-take] that
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
{-@ type Matrix a Rows Cols = List (List a Cols) Rows @-}
\end{code}

The `transpose` operation flips the rows and columns. I confess
can never really understand matrices without concrete examples, 
and even then, barely. So, lets say you have a "matrix"

~~~~~{.haskell}
m1  :: Matrix Int 4 2
m1  =  [ [1, 2]
       , [3, 4]
       , [5, 6] 
       , [7, 8] ]
~~~~~

then the matrix `m2 = transpose 2 3 m1` should be

~~~~~{.haskell}
m2 :: Matrix Int 2 4
m1  =  [ [1, 3, 5, 7]
       , [2, 4, 6, 8] ]
~~~~~

We will use a `Matrix a m n` to represent a *single cluster* of `m` points 
each of which has `n` dimensions. We will transpose the matrix to make it 
easy to *sum* and *average* the points along *each* dimension, in order to 
compute the *center* of the cluster.

As you can work out from the above, the code for `transpose` is quite
straightforward: each *output row* is simply the list of `head`s of 
the *input rows*:

\begin{code}
transpose                    :: Int -> Int -> [[a]] -> [[a]]
transpose 0 _ _              = []
transpose c r ((x:xs) : xss) = (x : map head xss) : transpose (c-1) r (xs : map tail xss)

-- Not needed, just for exposition
transpose c r ([] : _)       = liquidError "dead code" 
transpose c r []             = liquidError "dead code"
\end{code}

LiquidHaskell verifies that

\begin{code} 
{-@ transpose :: c:Int -> r:PosInt -> Matrix a r c -> Matrix a c r @-}
\end{code}

Lets see how. Lean in close.

First, LiquidHaskell use the fact that the third input is a `Matrix a r c`
that is a `List (List a c) r` to deduce that in the **input** list

- the length of the *outer* list `(len ((x:xs) : xss))` equals the number of *rows* `r`, 
- and hence, the length of the *outer tail* `(len xss)` equals `r-1`, and
- the length of the *inner* list `len (x:xs)` equals the number of *columns* `c`,
- and hence, the length of the *inner tail* `(len xs)` equals `c-1`.

Next, from the above, LiquidHaskell infers that in the recursive call

- the length of the *outer* list `(len (xs : map tail xss))` is `1 + (len xss)` that is *also* `r`
- the length of the *inner* list `(len xs)` is `c-1`

Finally, inductively the output of the recursive call is a `Matrix a (c-1) r` and so in the **output**, 

- the length of the *inner* list is `1 + (len xss)`, that is, `r`,
- the length of the *outer* list is `c`, that is, `1` plus the outer length `c-1` of the recursive result.

Thus, via SMT based reasoning, LiquidHaskell concludes that the output is
indeed `Matrix a c r` where the dimensions of the inner and outer lists are
flipped!

**Aside: Comprehensions** Incidentally, the code above is essentially that of `Data.List.transpose`
[from the Prelude][URL-transpose] except that we have added dimension parameters, used them to ensure 
that all rows have the same length, and to precisely characterize the shape of the input and output lists.

\begin{code}The Prelude implementation uses list comprehensions -- the second equation for `transpose` is 
transpose n m ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : transpose (n-1) m (xs : [ t | (_:t) <- xss])
\end{code}
We have used `map` and `head` and `tail` just for illustration -- the comprehension version works just fine -- 
go ahead and [demo it for yourself!][demo]

Intermission
------------

Time for a break -- [go see a cat video!][maru] -- or skip it, stretch your
legs, and return post-haste, for the [next installment][kmeans], in which 
we will use the types and functions described above, to develop the clustering
algorithm.

[safeList]:      /blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/ 
[kmeansI]:       /blog/2013/02/16/kmeans-clustering-I.lhs/
[kmeansII]:      /blog/2013/02/17/kmeans-clustering-II.lhs/
[URL-take]:      https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/GHC/List.lhs#L334
[URL-groupBy]:   http://hackage.haskell.org/packages/archive/base/latest/doc/html/Data-List.html#v:groupBy
[URL-transpose]: http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html#transpose
[maru]:          http://www.youtube.com/watch?v=8uDuls5TyNE
[demo]:          http://goto.ucsd.edu/~rjhala/liquid/haskell/demo/#?demo=KMeansHelper.hs
[URL-kmeans]:    http://hackage.haskell.org/package/kmeans

