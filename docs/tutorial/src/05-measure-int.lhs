Numeric Measures {#numericmeasure}
================

\begin{comment}
\begin{code}

{-@ LIQUID "--diff"           @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module NumericMeasures where
-- (
--   -- * Types
--     Vector (..), Matrix (..), List 
--   , dotProd, matProd
--   , dotProduct, matProduct, transpose
--   , vecFromList, matFromList
--   , map, take, take', drop, for, zip, zipOrNull, partition, reverse
--   , first, second, size, notEmpty
--   , test1, test2, test3, test4, test5, test6, ok23, ok32, bad1, bad2 
--   , vCons, vHd, vTl
--   ) where

import Prelude  hiding  (map, zipWith, zip, take, drop, reverse)

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg
take, drop, take' :: Int -> [a] -> [a]
txgo              :: Int -> Int -> Vector (Vector a) -> Vector (Vector a)
quickSort         :: (Ord a) => [a] -> [a]
\end{code}

Plan
----

1. Wholemeal Programming
2. Specifying Dimensions
3. Dimension-aware List API 
4. Dimension-safe Vectors and Matrices
5. Case Study: K-Means Clustering
\end{comment}

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
              deriving (Eq)
                         
data Matrix a = M { mRow  :: Int
                  , mCol  :: Int
                  , mElts :: Vector (Vector a)
                  }
              deriving (Eq)
\end{code}

\newthought{Vector Product} We can write the dot product of
two `Vector`s using a fold:

\begin{code}
dotProd       :: (Num a) => Vector a -> Vector a -> a
dotProd vx vy = sum (prod xs ys)
  where
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
matProd (M rx _ xs) (M _ cy ys)
                 = M rx cy elts
  where
    elts         = for xs $ \xi ->
                     for ys $ \yj ->
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
  while the implementation of  `matProd` breezes past GHC it is quite wrong!}


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


\begin{code}
{-@ measure size @-}
{- size    :: xs:[a] -> {v:Nat | v = size xs && v = len xs} @-}
{-@ size    :: xs:[a] -> Nat @-}
size        :: [a] -> Int
size (_:rs) = 1 + size rs
size []     = 0
\end{code}

\newthought{Measures Refine Constructors}
As with [refined data definitions](#autosmart), the
measures are translated into strengthened types for
the type's constructors. For example, the `size`
measure is translated into:

\begin{spec}
data [a] where
  []  :: {v: [a] | size v = 0}
  (:) :: x:a -> xs:[a] -> {v:[a] | size v = 1 + size xs}
\end{spec}

\newthought{Multiple Measures} We can write several
different measures for a datatype. For example, in
addition to the `size` measure, we can define a `notEmpty`
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
  []  :: {v: [a] | not (notEmpty v) && size v = 0}
  (:) :: x:a -> xs:[a] -> {v:[a] | notEmpty v && size v = 1 + size xs}
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

Lets use `size` to create a dimension-aware API for lists.
To get the ball rolling, lets defining a few helpful type aliases:

\newthought{An `N`-List} is a list with exactly `N` elements:
\footnotetext{Note that when defining refinement type aliases,
we use uppercase variables like `N` to distinguish value- parameters
from the lowercase type parameters like `a`.}

\begin{code}
{-@ type ListN a N = {v : [a] | size v = N} @-}
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
{-@ map      :: (a -> b) -> xs:List a -> ListN b (size xs) @-}
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

{-@ invariant {v:[a] | 0 <= size v} @-}

{-@ zipWith :: _ -> xs:List a -> ListN b (size xs) -> ListN c (size xs) @-}
zipWith f (a:as) (b:bs) = f a b : zipWith f as bs
zipWith _ [] []         = []
zipWith _ _  _          = die "no other cases"
\end{code}

\newthought{unsafeZip} The signature for `zipWith` is quite severe -- it
rules out the case where the zipping occurs only upto the shorter input.
Here's a function that actually allows for that case, where the output
type is the *shorter* of the two inputs:

\begin{code}
{-@ zip :: as:[a] -> bs:[b] -> {v:[(a,b)] | Min (size v) (size as) (size bs)} @-}
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

\exercisen{Zip Unless Empty} In my experience, `zip` as shown above is far too
permissive and lets all sorts of bugs into my code. As middle
ground, consider `zipOrNull` below. Write a specification
for `zipOrNull` such that the code below is verified by
LiquidHaskell:

\begin{code}
zipOrNull       :: [a] -> [b] -> [(a, b)]
zipOrNull [] _  = []
zipOrNull _ []  = []
zipOrNull xs ys = zipWith (,) xs ys

{-@ test1 :: {v: _ | size v = 2} @-}
test1     = zipOrNull [0, 1] [True, False]

{-@ test2 :: {v: _ | size v = 0} @-}
test2     = zipOrNull [] [True, False]

{-@ test3 :: {v: _ | size v = 0} @-}
test3     = zipOrNull ["cat", "dog"] []
\end{code}

\hint Yes, the type is rather gross; it uses a bunch of
      disjunctions `||` , conjunctions `&&` and implications `=>`.

\exercisen{Reverse} Consider the code below that reverses
a list using the tail-recursive `go`. Fix the signature for `go`
so that LiquidHaskell can prove the specification for `reverse`.

\begin{code}
{-@ reverse       :: xs:[a] -> {v:[a] | size v = size xs} @-}
reverse xs        = go [] xs
  where 
    {-@ go        :: xs:[a] -> ys:[a] -> [a] @-}
    go acc []     = acc
    go acc (x:xs) = go (x:acc) xs
\end{code}

\hint How big is the list returned by `go`?

Lists: Size Reducing API {#listreducing} 
------------------------

Next, lets look at some functions that truncate lists, in one way or another.

\newthought{Take} lets us grab the first `k` elements from a list: 

\begin{code}
{-@ take'     :: n:Nat -> {v:List a | n <= size v} -> ListN a n @-}
take' 0 _      = []
take' n (x:xs) = x : take' (n-1) xs
take' _ _      = die "won't  happen"
\end{code}


\exercisen{Drop} is the yang to `take`'s yin: it returns
the remainder after extracting the first `k` elements.
Write a suitable specification for it so that the below
typechecks:

\begin{code}
drop 0 xs     = xs
drop n (_:xs) = drop (n-1) xs
drop _ _      = die "won't happen"

{-@ test4 :: ListN String 2 @-}
test4 = drop 1 ["cat", "dog", "mouse"] 
\end{code}

\exercisen{Take it easy} The version `take'` above is too restrictive;
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
partition _ []     = ([], [])
partition f (x:xs)
  | f x            = (x:ys, zs)
  | otherwise      = (ys, x:zs)
  where
    (ys, zs)       = partition f xs
\end{code}

We would like to specify that the *sum* of the output tuple's
dimensions equal the input list's dimension.
Lets write measures to access the elements of the output:

\begin{code}
{-@ measure first @-}
first  (x, _) = x

{-@ measure second @-}
second (_, y) = y
\end{code}

\noindent We can use the above to type `partition` as

\begin{code}
{-@ partition :: (a -> Bool) -> xs:_ -> ListPair a (size xs) @-}
\end{code}

\noindent using an alias for a pair of lists whose total dimension equals `N`

\begin{code}
{-@ type ListPair a N = {v:([a], [a]) | size (first v) + size (second v) = N} @-}
\end{code}

\exercisen{QuickSort} Use the `partition` function above to implement `quickSort`:

\begin{code}
-- >> quickSort [1,4,3,2]
-- [1,2,3,4]

{-@ quickSort    :: (Ord a) => xs:List a -> ListN a (size xs) @-}
quickSort []     = []
quickSort (x:xs) = undefined

{-@ test10 :: ListN String 2 @-}
test10 = quickSort test4 
\end{code}


Dimension Safe Vector API
-------------------------

We can use the dimension aware lists to create a safe vector API.

\newthought{Legal Vectors} are those whose `vDim` field actually equals the size of the underlying list:

\begin{code}
{-@ data Vector a = V { vDim  :: Nat
                      , vElts :: ListN a vDim }
  @-}
\end{code}

\noindent 
The refined data type prevents the creation of illegal vectors:

\begin{code}
okVec  = V 2 [10, 20]       -- accepted by LH

badVec = V 2 [10, 20, 30]   -- rejected by LH
\end{code}

\newthought{Access} Next, lets write some functions to access the elements of a vector:

\begin{code}
{-@ vCons        :: a -> x:Vector a -> {v:Vector a | vDim v = vDim x + 1} @-}
vCons x (V n xs) = V (n+1) (x:xs)

{-@ type VectorNE a = {v:Vector a | vDim v > 0} @-}

{-@ vHd :: VectorNE a -> a @-}
vHd (V _ (x:_)) = x
vHd _           = die "nope"

{-@ vTl          :: x:VectorNE a -> {v:Vector a | vDim v = vDim x - 1} @-}
vTl (V n (_:xs)) = V (n-1) xs 
vTl _           = die "nope"
\end{code}

\newthought{Iteration} It is straightforward to see that:

\begin{code}
{-@ for :: x:Vector a -> (a -> b) -> VectorN b (vDim x) @-}
\end{code}
\newthought{Binary Operations} We want to apply various binary
operations to *compatible* vectors, i.e. vectors with equal
dimensions. To this end, it is handy to have an alias for
vectors of a given size:

\begin{code}
{-@ type VectorN a N = {v:Vector a | vDim v = N} @-}
\end{code}

\noindent We can now write a generic binary operator:

\begin{code}
{-@ vBin :: (a -> b -> c) -> vx:Vector a -> vy:VectorN b (vDim vx) -> VectorN c (vDim vx) @-}
vBin     :: (a -> b -> c) -> Vector a -> Vector b -> Vector c
vBin op (V n xs) (V _ ys) = V n (zipWith op xs ys)
\end{code}

\newthought{Dot Product} Finally, we can implement a wholemeal,
dimension safe dot product operator as:

\begin{code}
{-@ dotProduct :: (Num a) => x:Vector a -> y:VectorN a (vDim x) -> a @-}
dotProduct x y = sum $ vElts $ vBin (*) x y 
\end{code}

\exercisen{Vector Constructor} Complete the *specification* and
*implementation* of `vecFromList` which *creates* a `Vector` from
a plain old list.

\begin{code}
vecFromList     :: [a] -> Vector a
vecFromList xs  = undefined

test6  = dotProduct vx vy    -- should be accepted by LH
  where 
    vx = vecFromList [1,2,3]
    vy = vecFromList [4,5,6]
\end{code}

Dimension Safe Matrix API 
-------------------------

The same methods let us create a dimension safe Matrix API which
ensures that only legal matrices are created and that operations
are performed on compatible matrices.

\newthought{Legal Matrices} are those where the dimension of the
outer vector equals the number of rows `mRow` and the dimension
of each inner vector is `mCol`. We can specify legality in a
refined data definition: 

\begin{code}
{-@ data Matrix a = M { mRow  :: Pos
                      , mCol  :: Pos 
                      , mElts :: VectorN (VectorN a mCol) mRow
                      }
  @-}
\end{code}

\noindent Notice that we avoid disallow degenerate matrices by
requiring the dimensions to be positive.

\begin{code}

{-@ type Pos = {v:Int | 0 < v} @-}
\end{code}

\noindent It is convenient to have an alias for matrices of a given size:

\begin{code}
{-@ type MatrixN a R C = {v:Matrix a | mRow v = R && mCol v = C} @-}
\end{code}

\noindent after LiquidHaskell accepts:

\begin{code}
ok23      = M 2 3 (V 2 [ V 3 [1, 2, 3]
                       , V 3 [4, 5, 6] ])
\end{code}

\exercisen{Legal Matrix} Modify the definitions of `bad1` and `bad2`
so that they are legal matrices accepted by LiquidHaskell.

\begin{code}
bad1 :: Matrix Int
bad1 = M 2 3 (V 2 [ V 3 [1, 2   ]
                  , V 3 [4, 5, 6]])

bad2 :: Matrix Int
bad2 = M 2 3 (V 2 [ V 2 [1, 2]
                  , V 2 [4, 5] ])
\end{code}

\exercisen{Matrix Constructor} \singlestar Write a function to construct a `Matrix` from a nested list.

\begin{code}
matFromList      :: [[a]] -> Maybe (Matrix a)
matFromList []   = Nothing                       -- no meaningful dimensions! 
matFromList xss@(xs:_)
  | ok           = Just (M r c vs) 
  | otherwise    = Nothing 
  where
    r            = size xss
    c            = size xs
    ok           = undefined
    vs           = undefined 

\end{code}

\exercisen{Refined Matrix Constructor} \doublestar Refine the
specification for `matFromList` so that the following is
accepted by LiquidHaskell:

\begin{code}
{-@ mat23 :: Maybe (MatrixN Integer 2 2) @-} 
mat23     = matFromList [ [1, 2]
                        , [3, 4] ]
\end{code}

\hint It is easy to specify the number of rows from `xss`.
How will you figure out the number of columns? A measure
may be useful.

\begin{comment}
-- DELETE ME
{-@ matFromList  :: xss:[[a]] -> Maybe (MatrixN a (size xss) (cols xss)) @-}
{-@ measure cols @-}
{-@ cols   :: [[a]] -> Nat @-}
cols (r:_) = size r
cols []    = 0
\end{comment}

\newthought{Matrix Multiplication} Ok, lets now implement
matrix multiplication. You'd think we did it already, but
in fact the implementation at the top of this chapter
is all wrong.
\footnotetext{You could run it of course, or you could
just replace `dotProd` with our type-safe `dotProduct`
and see what happens!}
Indeed, you cannot just multiply any two matrices: the
number of *columns* of the first must equal to the *rows*
of the second -- after which point the result comprises
the `dotProduct` of the rows of the first matrix with
the columns of the second.

\begin{code}
{-@ matProduct   :: (Num a) => x:Matrix a
                            -> y:{Matrix a  | mCol x = mRow y}
                            -> MatrixN a (mRow x) (mCol y)
  @-}
matProduct (M rx _ xs) my@(M _ cy _)
                 = M rx cy elts
  where
    elts         = for xs $ \xi ->
                     for ys' $ \yj ->
                       dotProduct xi yj
    M _ _ ys'    = transpose my 
\end{code}

\newthought{Transposition} To iterate over the columns of
`my` we just `transpose` it so the columns become rows.

\begin{code}
-- >>> ok32 == transpose ok23
-- True
ok32 = M 3 2 (V 3 [ V 2 [1, 4]
                  , V 2 [2, 5]
                  , V 2 [3, 6] ])
\end{code}

\exercisen{Matrix Transposition} \doublestar
Use the `Vector` API to Complete the implementation of `txgo`.
For inspiration, you might look at the implementation of
`Data.List.transpose` from the [prelude][URL-transpose].
Better still, don't.

\begin{code}
{-@ transpose          :: m:Matrix a -> MatrixN a (mCol m) (mRow m) @-}
transpose (M r c rows) = M c r $ txgo c r rows

{-@ txgo      :: c:Nat -> r:Nat
              -> VectorN (VectorN a c) r
              -> VectorN (VectorN a r) c @-}
txgo c r rows = undefined
\end{code}

\hint As shown by `ok23` and `ok32`, `transpose` works by
stripping out the `head`s of the input rows, to create the
corresponding output rows.

Recap
-----

In this chapter, we saw how to use measures to describe
numeric properties of structures like lists (`Vector`)
and nested lists (`Matrix`). To recap:

1. Measures are *structurally recursive* functions, with a single
   equation per data constructor,

2. Measures can be used to create refined data definitions
   that prevent the creation of illegal values,

3. Measures can then be used to enable safe wholemeal programming,
   via dimension-aware APIs that ensure that operators only apply to
   compatible values. 

We can use numeric measures to encode various other properties
of structures; in subsequent chapters we will see examples ranging
from high-level [height-balanced trees](#case-study-wbl), to low-level
safe [pointer arithmetic](#case-study-pointers).


