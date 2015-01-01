Numeric Measures
================


\begin{code}

{-@ LIQUID "--diff"           @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module NumericMeasures where

import qualified Data.List as L
import Prelude                          hiding  (zipWith)

\end{code}

- 1. Tracking Dimensions "Wholemeal Programming"
      * vector/dotProd
      * matrix/matMult

      * zipWith
      * dotProt
      
-- 2. Defining Numeric Measures
-- 3. Using Numeric Measures

Some of the programs *going wrong* -- and, hence, use cases for LiquidHaskell -- that
we've seen so far, are a consequence of what \cite{Bird} calls *indexitis*
a tendency  to manipulate and hence worry about the low-level details of iterating over an array by keeping track
of a current index. Indeed, functional languages like Haskell encourage
[wholemeal programming]

http://www.cs.ox.ac.uk/ralf.hinze/publications/ICFP09.pdf),
“Functional languages excel at wholemeal programming, a term coined by Geraint Jones. Wholemeal programming means to think big: work with an entire list, rather than a sequence of elements; develop a solution space, rather than an individual solution; imagine a graph, rather than a single path. The wholemeal approach often offers new insights or provides new perspectives on a given problem. It is nicely complemented by the idea of projective programming: first solve a more general problem, then extract the interesting bits and pieces by transforming the general program into more specialised ones.”

Some of the examples 
The examples we've seen so far are rather simple.


\begin{code}
for = flip map

mult m1 m2      = for m1 $ \ri ->
                    for m2' $ \cj ->
                      dotProd ri cj
  where
    m2'         = L.transpose m2 
    dotProd x y = sum $ L.zipWith (*) x y
\end{code}

[Last time][safeList] we introduced a new specification mechanism called a
*measure* and demonstrated how to use it to encode the *length* of a list.
We saw how measures could be used to verify that functions like `head` and
`tail` were only called with non-empty lists (whose length was strictly
positive). As several folks pointed out, once LiquidHaskell can reason about
lengths, it can do a lot more than just analyze non-emptiness.

Indeed!

Over the next *two* posts, lets see how one might implement a Kmeans
algorithm that clusters `n`-dimensional points groups, and how LiquidHaskell
can help us write and enforce various dimensionality invariants along the way.

Rather than reinvent the wheel, we will modify an existing implementation
of K-Means, [available on hackage][URL-kmeans]. This may not be the
most efficient implementation, but its a nice introduction to the algorithm,
and the general invariants will hold for more sophisticated implementations.

We have broken this entry into two convenient, bite-sized chunks:

+ **Part I**  Introduces the basic types and list operations needed by KMeans,

+ **Part II** Describes how the operations are used in the KMeans implementation.

The Game: Clustering Points
---------------------------

The goal of [K-Means clustering](http://en.wikipedia.org/wiki/K-means_clustering)
is the following. Given

- **Input** : A set of *points* represented by *n-dimensional points*
  in *Euclidian* space, return

- **Output** : A partitioning of the points, into K clusters, in a manner that
  minimizes sum of distances between each point and its cluster center.


The Players: Types
------------------

Lets make matters concrete by creating types for the different elements of the algorithm.

**1. Fixed-Length Lists**  We will represent n-dimensional points using
good old Haskell lists, refined with a predicate that describes the
dimensionality (i.e. length.) To simplify matters, lets package this
into a *type alias* that denotes lists of a given length `N`.

\begin{code}
{-@ type List a N = {v : [a] | (len v) = N} @-}
\end{code}

**2. Points** Next, we can represent an `N`-dimensional point as list of `Double` of length `N`,

\begin{code}
{-@ type Point N = List Double N @-}
\end{code}

**3. Clusters** A cluster is a **non-empty** list of points,

\begin{code}
{-@ type NonEmptyList a = {v : [a] | (len v) > 0} @-}
\end{code}

**4. Clustering** And finally, a clustering is a list of (non-empty) clusters.

\begin{code}
{-@ type Clustering a  = [(NonEmptyList a)] @-}
\end{code}

**Notation:** When defining refinement type aliases, we use uppercase variables like `N`
to distinguish value- parameters from the lowercase type parameters like `a`.


**Aside:** By the way, if you are familiar with the *index-style* length
encoding e.g. as found in [DML][dml] or [Agda][agdavec], then its worth
noting that despite appearances, our `List` and `Point` definitions are
*not* indexed. We're just using the indices to define abbreviations for the
refinement predicates, and we have deliberately chosen the predicates to
facilitate SMT based checking and inference.

Basic Operations on Points and Clusters
=======================================

Ok, with the types firmly in hand, let us go forth and develop the KMeans
clustering implementation. We will use a variety of small helper functions
(of the kind found in `Data.List`.) Lets get started by looking at them
through our newly *refined* eyes.

Grouping
--------

The first such function is [groupBy][URL-groupBy]. We can
refine its type so that instead of just producing a `[[a]]`
we know that it produces a `Clustering a` which is a list
of *non-empty* lists.

\begin{code}
{-@ groupBy       ::(a -> a -> Bool) -> [a] -> (Clustering a) @-}
groupBy _  []     = []
groupBy eq (x:xs) = (x:ys) : groupBy eq zs
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
{-@ partition :: size:PosInt -> [a] -> (Clustering a) @-}
{-@ type PosInt = {v: Int | v > 0 } @-}
\end{code}

which is given a *strictly positive* integer argument,
a list of `a` values, and returns a `Clustering a`,
that is, a list of non-empty lists. (Each inner list has a length
that is less than `size`, but we shall elide this for simplicity.)

The function is implemented in a straightforward manner, using the
library functions `take` and `drop`

\begin{code}
partition _    []       = []
partition size ys@(_:_) = zs : partition size zs'
  where
    zs                  = take size ys
    zs'                 = drop size ys
\end{code}

To verify that a valid `Clustering` is produced, LiquidHaskell needs only
verify that the list `zs` above is non-empty, by suitably connecting the
properties of the inputs `size` and `ys` with the output.

We have [verified elsewhere][URL-take] that

\begin{spec}
take :: n:{v: Int | v >= 0 }
     -> xs:[a]
     -> {v:[a] | (len v) = (if ((len xs) < n) then (len xs) else n) }
\end{spec}

In other words, the output list's length is the *smaller of* the input
list's length and `n`.  Thus, since both `size` and the `(len ys)` are
greater than `1`, LiquidHaskell deduces that the list returned by `take
size ys` has a length greater than `1`, i.e., is non-empty.

Zipping
-------

To compute the *Euclidean distance* between two points, we will use
the `zipWith` function. We must make sure that it is invoked on points
with the same number of dimensions, so we write

\begin{code}
{-@ zipWith :: (a -> b -> c)
            -> xs:[a] -> (List b (len xs)) -> (List c (len xs)) @-}
zipWith f (a:as) (b:bs) = f a b : zipWith f as bs
zipWith _ [] []         = []
\end{code}

The type stipulates that the second input list and the output have
the same length as the first input. Furthermore, it rules out the
case where one list is empty and the other is not, as in that case
the former's length is zero while the latter's is not.

Transposing
-----------

The last basic operation that we will require is a means to
*transpose* a `Matrix`, which itself is just a list of lists:

\begin{code}
{-@ type Matrix a Rows Cols = (List (List a Cols) Rows) @-}
\end{code}

The `transpose` operation flips the rows and columns. I confess that I
can never really understand matrices without concrete examples,
and even then, barely.

So, lets say we have a *matrix*

\begin{spec}
m1  :: Matrix Int 4 2
m1  =  [ [1, 2]
       , [3, 4]
       , [5, 6]
       , [7, 8] ]
\end{spec}

then the matrix `m2 = transpose 2 3 m1` should be

\begin{spec}
m2 :: Matrix Int 2 4
m2  =  [ [1, 3, 5, 7]
       , [2, 4, 6, 8] ]
\end{spec}

We will use a `Matrix a m n` to represent a *single cluster* of `m` points
each of which has `n` dimensions. We will transpose the matrix to make it
easy to *sum* and *average* the points along *each* dimension, in order to
compute the *center* of the cluster.

As you can work out from the above, the code for `transpose` is quite
straightforward: each *output row* is simply the list of `head`s of
the *input rows*:

\begin{code}
transpose       :: Int -> Int -> [[a]] -> [[a]]
transpose 0 _ _ = []
transpose c r ((col00 : col01s) : row1s)
  = row0' : row1s'
    where
      row0'     = col00  : [ col0  | (col0 : _)  <- row1s ]
      rest      = col01s : [ col1s | (_ : col1s) <- row1s ]
      row1s'    = transpose (c-1) r rest
\end{code}

LiquidHaskell verifies that

\begin{code}
{-@ transpose :: c:Int -> r:PosInt -> Matrix a r c -> Matrix a c r @-}
\end{code}

Try to work it out for yourself on pencil and paper.

If you like you can get a hint by seeing how LiquidHaskell figures it out.
Lets work *backwards*.

LiquidHaskell verifies the output type by inferring that

\begin{spec}
row0'        :: (List a r)
row1s'       :: List (List a r) (c - 1) -- i.e. Matrix a (c - 1) r
\end{spec}

and so, by simply using the *measure-refined* type for `:`

\begin{spec}
(:)          :: x:a -> xs:[a] -> { v : [a] | (len v) = 1 + (len xs) }
\end{spec}

LiquidHaskell deduces that

\begin{spec}
row0 : rows' :: List (List a r) c
\end{spec}

That is,

\begin{spec}
row0 : rows' :: Matrix a c r
\end{spec}

Excellent! Now, lets work backwards. How does it infer the types of `row0'` and `row1s'`?

The first case is easy: `row0'` is just the list of *heads* of each row, hence a `List a r`.

Now, lets look at `row1s'`. Notice that `row1s` is the matrix of all *except* the first row of the input Matrix, and so

\begin{spec}
row1s        :: Matrix a (r-1) c
\end{spec}

and so, as

\begin{spec}
col01s       :: List a (c-1)
col1s        :: List a (c-1)
\end{spec}

LiquidHaskell deduces that since `rest` is the concatenation of `r-1` tails from `row1s`

\begin{spec}
rest         = col01s : [ col1s | (_ : col1s) <- row1s ]
\end{spec}

the type of `rest` is

\begin{spec}
rest         :: List (List a (c - 1)) r
\end{spec}

which is just

\begin{spec}
rest         :: Matrix a r (c-1)
\end{spec}

Now, LiquidHaskell deduces `row1s' :: Matrix a (c-1) r` by inductively
plugging in the output type of the recursive call, thereby checking the
function's signature.

*Whew!* That was a fair bit of work, wasn't it!

Happily, we didn't have to do *any* of it. Instead, using the SMT solver,
LiquidHaskell ploughs through calculations like that and guarantees to us
that `transpose` indeed flips the dimensions of the inner and outer lists.

**Aside: Comprehensions vs. Map** Incidentally, the code above is essentially
that of `transpose` [from the Prelude][URL-transpose] with some extra
local variables for exposition. You could instead use a `map head` and `map tail`
and I encourage you to go ahead and [see for yourself.][demo]

Intermission
------------

Time for a break -- [go see a cat video!][maru] -- or skip it, stretch your
legs, and return post-haste for the [next installment][kmeansII], in which
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
[dml]:           http://www.cs.bu.edu/~hwxi/DML/DML.html
[agdavec]:       http://code.haskell.org/Agda/examples/Vec.agda

