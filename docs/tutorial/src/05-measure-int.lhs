Numeric Measures
================

\begin{code}

{-@ LIQUID "--diff"           @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module NumericMeasures where

import qualified Data.List as L
import Data.List (foldl')
import Prelude  hiding  (map, zipWith, zip, take, drop)

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg
take, drop, take' :: Int -> [a] -> [a]
\end{code}

Plan
----

1. Wholemeal Programming
2. Specifying Dimensions
3. Dimension-aware List API 
4. Dimension-safe Vectors and Matrices
5. Case Study: K-Means Clustering

Many of the programs we have seen so far, for example those in
[here](#vectorbounds), suffer from *indexitis*
\footnotetext{A term coined by [Richard Bird][bird-pearls]}
a tendency to perform low-level manipulations to iterate over the
indices into a collection, which opens the door to various off-by-one
errors. Such errors can be entirely eliminated by instead programming
at a higher level, using a [wholemeal approach][hinze-icfp09]
where the emphasis is on using aggregate operations, like `map`,
`fold` and `reduce`. However, wholemeal programming requires us to
take care when operating on multiple collections; if these collections
are *incompatible*, e.g. have the wrong dimensions, then we end up with
a fate worse than a crash, a *meaningless* result.

Fortunately, LiquidHaskell can help. Lets see how we can use measures to
specify dimensions and create a dimension-aware API for lists which can be
used to implement wholemeal dimension-safe APIs.
\footnotetext{In a [later chapter](#kmeans-case-study) we will use this
API to implement K-means clustering.}


Wholemeal Programming
---------------------

Indexitis begone! As an example of wholemeal programming, lets
write a small library that represents vectors as lists and
matrices as nested vectors:

\begin{code}
data Vector a = V { vDim  :: Int
                  , vElts :: [a]
                  }

data Matrix a = M { mRow  :: Int
                  , mCol  :: Int
                  , mElts :: Vector (Vector a)
                  }
\end{code}

\newthought{Vector Product} We can write the dot product of
two `Vector`s using a fold:

\begin{code}
dotProd       :: (Num a) => Vector a -> Vector a -> a
dotProd vx vy = sum (prod xs ys)
  where
    sum       = foldl' (+) 0
    prod      = zipWith (\x y -> x * y)
    xs        = vElts vx
    ys        = vElts vy
\end{code}

\newthought{Matrix Product} Similarly, we can compute the
product of two matrices in a wholemeal fashion, without 
performing any low-level index manipulations, but instead using
a high-level "iterator" over the elements of the matrix.

\begin{code}
matProd       :: (Num a) => Matrix a -> Matrix a -> Matrix a
matProd mx my = M (mRow mx) (mCol my) elts
  where
    elts      = for (mElts mx) $ \xi ->
                  for (mElts my) $ \yj ->
                    dotProd xi yj
\end{code}

\newthought{Iteration} In the above, the "iteration" embodied
in `for` is simply a `map` over the elements of the vector.

\begin{code}
for (V n xs) f = V n (map f xs) 
\end{code}

\newthought{Wholemeal programming frees} us from having to fret
about low-level index range manipulation, but is hardly a panacea.
Instead, we must now think carefully about the *compatibility*
of the various aggreates. For example,

+ `dotProd` is only sensible on vectors of the same dimension;
  if one vector is shorter than another (i.e. has fewer elements)
  then we will won't get a run-time crash but instead will get
  some gibberish result that will be dreadfully hard to debug.

+ `matProd` is only well defined on matrices of compatible
  dimensions; the number of columns of `mx` must equal the
  number of rows  of `my`. Otherwise, again, rather than an
  error, we will get the wrong output. \footnotetext{In fact,
  while the above implementation happily breezes past GHC it
  is quite wrong!}


Specifying List Dimensions
--------------------------

In order to start reasoning about dimensions, we need a way
to represent the *dimension* of a list inside the refinement
logic. \footnotetext{We could just use `vDim`, but that is
a lazy cheat as there is no guarantee that the field's value
actually equals the size of the list!}

\newthought{Measures} are ideal for this
task. [Previously](#boolmeasures) we saw how we could lift Haskell
functions up to the refinement logic.
\footnotetext{Recall that these must be inductively defined functions,
with a single equation per data-constructor}
Lets write a measure to describe the length of a list:

\begin{spec}
{-@ measure len @-}
len        :: [a] -> Int
len []     = 0
len (_:xs) = 1 + len xs
\end{spec}

\newthought{Measures Refine Constructors}
As with [refined data definitions](#autosmart), the
measures are translated into strengthened types for
the type's constructors. For example, the `len`
measure is translated into:

\begin{spec}
data [a] where
  []  :: {v: [a] | len v = 0}
  (:) :: x:a -> xs:[a] -> {v:[a] | len v = 1 + len xs}
\end{spec}

\newthought{Multiple Measures} We can write several
different measures for a datatype. For example, in
addition to the `len` measure, we can define a `notEmpty`
measure for the list type:

\begin{code}
{-@ measure notEmpty @-}
notEmpty       :: [a] -> Bool
notEmpty []    = False
notEmpty (_:_) = True 
\end{code}

\newthought{Composing Measures}
LiquidHaskell lets you *compose* the different measures
simply by *conjoining* the refinements in the strengthened
constructors. For example, the two measures for lists end
up yielding the constructors:

\begin{spec}
data [a] where
  []  :: {v: [a] | not (notEmpty v) && len v = 0}
  (:) :: x:a -> xs:[a] -> {v:[a] | notEmpty v && len v = 1 + len xs}
\end{spec}

\noindent 
This is a very significant advantage of using measures
instead of indices as in [DML][dml] or [Agda][agdavec],
as *decouples property from structure*, which crucially
enables the use of the same structure for many different
purposes. That is, we need not know *a priori* what indices
to bake into the structure, but can define a generic
structure and refine it *a posteriori* as needed with
new measures.

Lets use `len` to create a dimension-aware API for lists.
To get the ball rolling, lets defining a few helpful type aliases:

\newthought{An `N`-List} is a list with exactly `N` elements:
\footnotetext{Note that when defining refinement type aliases,
we use uppercase variables like `N` to distinguish value- parameters
from the lowercase type parameters like `a`.}

\begin{code}
{-@ type ListN a N = {v : [a] | len v = N} @-}
\end{code}

\noindent To make the signatures symmetric, lets use an alias
for plain old Lists:

\begin{code}
type List a = [a]
\end{code}

Lists: Size Preserving API
--------------------------

With the types firmly in hand, let us write dimension-aware
variants of the usual list functions. The implementations are
the same as in the standard library i.e. [`Data.List`][data-list];
but the specifications are enriched with dimension information.

\newthought{`map`} yields a list with the same size as the input:

\begin{code}
{-@ map      :: (a -> b) -> xs:List a -> ListN b (len xs) @-}
map _ []     = []
map f (x:xs) = f x : map f xs
\end{code}

\newthought{zipWith} requires both lists to have the *same* size, and produces
a list with that same size.
\footnotetext{Note that as made explicit by the call to `die`, the
input type *rules out* the case where one list is empty and the other
is not, as in that case the former's length is zero while the latter's
is not, and hence, different.}

\begin{code}
{-@ zipWith :: _ -> xs:List a -> ListN b (len xs) -> ListN c (len xs) @-}
zipWith f (a:as) (b:bs) = f a b : zipWith f as bs
zipWith _ [] []         = []
zipWith _ _  _          = die "no other cases"
\end{code}

\newthought{unsafeZip} The signature for `zipWith` is quite severe -- it
rules out the case where the zipping occurs only upto the shorter input.
Here's a function that actually allows for that case, where the output
type is the *shorter* of the two inputs:

\begin{code}
{-@ zip :: as:[a] -> bs:[b] -> {v:[(a,b)] | Min (len v) (len as) (len bs)} @-}
zip (a:as) (b:bs) = (a, b) : zip as bs
zip [] _          = []
zip _  []         = [] 
\end{code}

\noindent The output type uses the following which defines `X`
to be the smaller of `Y` and `Z`.
\footnotetext{Note that `if p then q else r` is simply an abbreviation for `p => q && not p => r`}

\begin{code}
{-@ predicate Min X Y Z = (if X < Y then X = Y else X = Z) @-}
\end{code}

\exercise In my experience, `zip` as shown above is far too
permissive and lets all sorts of bugs into my code. As middle
ground, consider `zipOrNull` below. Write a specification
for `zipOrNull` such that the code below is verified by
LiquidHaskell:

\begin{code}
zipOrNull [] _  = []
zipOrNull _ []  = []
zipOrNull xs ys = zipWith (,) xs ys

{-@ test1 :: {v: _ | len v = 2} @-}
test1     = zipOrNull [0, 1] [True, False]

{-@ test2 :: {v: _ | len v = 0} @-}
test2 = zipOrNull [] [True, False]

{-@ test3 :: {v: _ | len v = 0} @-}
test3 = zipOrNull [0, 1] []
\end{code}

\hint Yes, the type is rather gross; it uses a bunch of
      disjunctions `||` , conjunctions `&&` and implications `=>`.

\exercise {} **[Reverse]** Consider the code below that reverses
a list using the tail-recursive `go`. Fix the signature for `go`
so that LiquidHaskell can prove the specification for `reverse`.

\begin{code}
{-@ reverse       :: xs:[a] -> {v:[a] | len v = len xs} @-}
reverse xs        = go [] xs
  where 
    {-@ go        :: xs:[a] -> ys:[a] -> [a] @-}
    go acc []     = acc
    go acc (x:xs) = go (x:acc) xs
\end{code}

\hint How big is the list returned by `go`?

Lists: Size Reducing API 
------------------------

Next, lets look at some functions that truncate lists, in one way or another.

\newthought{Take} lets us grab the first `k` elements from a list: 

\begin{code}
{-@ take'     :: n:Nat -> {v:List a | n <= len v} -> ListN a n @-}
take' 0 _      = []
take' n (x:xs) = x : take' (n-1) xs
take' _ _      = die "won't  happen"
\end{code}

\exercise {} **[Drop]** is the yang to `take`'s yin: it returns the
remainder after extracting the first `k` elements: 

\begin{code}
drop 0 xs     = xs
drop n (_:xs) = drop (n-1) xs
drop _ _      = die "won't happen"

{-@ test4 :: ListN String 2 @-}
test4 = drop 1 ["cat", "dog", "mouse"] 
\end{code}

\exercise {} The version `take'` above is too restrictive;
it insists that the list actually have at least `n` elements.
Modify the signature for the *real* `take` function so that
the code below is accepted by LiquidHaskell:

\begin{code}
take 0 _       = []
take _ []      = []
take n (x:xs)  = x : take (n-1) xs

{-@ test5 :: [ListN String 2] @-}
test5 = [ take 2  ["cat", "dog", "mouse"]
        , take 20 ["cow", "goat"]        ] 
\end{code}

\newthought{Partition} As one last example, lets look at the
function that `partition`s a list using a user supplied predicate:

\begin{code}
{-@ partition :: xs:_ -> {v:_ | 1 + len (first v) + len (second v) = len x} @-}
partition _ []     = ([], [])
partition f (x:xs)
  | f x            = (x:ys, zs)
  | otherwise      = (ys, x:zs)
  where
    (ys, zs)       = partition f xs
\end{code}

We would like to specify that the *sum* of the output tuple's dimensions
equal the input list's dimension. Lets write measures to access the elements of the output:

\begin{code}
{-@ measure first @-}
first  (x, _) = x

{-@ measure second @-}
second (_, y) = y
\end{code}

\noindent We can use the above to type `partition` as

\begin{code}
\end{code}

-------------------------

\newthought{Legal Vectors}

\newthought{Vector Addition}

\newthought{Vector Multiplication}


Dimension Safe Matrix API 
-------------------------

\newthought{Legal Matrices}

\newthought{Matrix Multiplication}

\newthought{Matrix Transposition}

The last basic operation that we will require is a means to
*transpose* a `Matrix`, which itself is just a list of lists:

\begin{code}
{- type Matrix a Rows Cols = (List (List a Cols) Rows) @-}
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
{- transpose :: c:Int -> r:PosInt -> Matrix a r c -> Matrix a c r @-}
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
(:)          :: x:a -> xs:[a] -> { v : [a] | len v = 1 + len xs }
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


