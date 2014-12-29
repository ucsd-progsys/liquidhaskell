Polymorphism
============

\begin{comment}
\begin{code}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--diff"           @-}
{-@ LIQUID "--no-termination" @-}

module VectorBounds 
   ( safeLookup 
   , unsafeLookup
   , vectorSum, vectorSum'
   , absoluteSum, absoluteSum' 
   , dotProduct
   , sparseProduct, sparseProduct'
   , eeks
   , startElem, startElem'
   ) where

import Prelude      hiding (abs, length)
import Data.List    (foldl')
import Data.Vector  hiding (foldl') 

sparseProduct, sparseProduct'  :: Vector Int -> [(Int, Int)] -> Int
\end{code}
\end{comment}

Refinement types start to shine when we want to establish
properties of *polymorphic*, datatypes and higher-order
functions. Rather than discuss these notions abstractly,
lets illustrate them with a [classic][dmlarray] use-case.

\newthought{Array Bounds Checking} aims to ensure that the
indices used to look up an array, are indeed *valid* for
the array, i.e. are between `0` and the *size* of the array.
For example, suppose we create an `array` with two elements,
and then attempt to look it up at various indices:

\begin{code}
twoLangs  = fromList ["haskell", "javascript"]

eeks      = [ok, yup, nono]
  where
    ok    = twoLangs ! 0
    yup   = twoLangs ! 1
    nono  = twoLangs ! 3
\end{code}

If we try to *run* the above, we get a nasty shock:

\begin{shell}
Prelude> :l 03-poly.lhs
[1 of 1] Compiling VectorBounds     ( 03-poly.lhs, interpreted )
Ok, modules loaded: VectorBounds.
*VectorBounds> eeks
Loading package ... done.
"*** Exception: ./Data/Vector/Generic.hs:249 ((!)): index out of bounds (3,2)
\end{shell}

The exception says we're trying to look up `array` at
index `3` whereas the size of `array` is just `2`.

If you load this file in a suitably LH-configured editor
(e.g. Vim or Emacs), you will literally see the error
*without* running the code. Next, lets see how LH checks
`ok` and `yup` but flags `nono`, and along the way,
learn how LiquidHaskell reasons about *recursion*,
*higher-order functions*, *data types*, and
*polymorphism*.


Specification: Vector Bounds {#vectorbounds}
--------------------------------------------

First, lets see how to *specify* array bounds safety by *refining* 
the types for the [key functions][vecspec] exported by `Data.Vector`. 
In particular we need a way to

1. *define* the size of a `Vector`
2. *compute* the size of a `Vector`
3. *restrict* the indices to those that are valid for a given size.

\newthought{Importing Specifications}
We can write specifications for imported modules -- for which we *lack* --
the code either directly in the source file or better, in `.spec` files
which can be reused by different client modules.
For example, we can write specifications for `Data.Vector` inside
`/include/Data/Vector.spec` which contains:

\begin{spec}
-- | Define the size 
measure vlen  :: Vector a -> Int 

-- | Compute the size 
assume length :: x:Vector a -> {v:Int | v = vlen x}

-- | Restrict the indices 
assume !      :: x:Vector a -> {v:Nat | v < vlen x} -> a 
\end{spec}

\newthought{Measures} are used to define *properties* (of Haskell data values) that  
are useful for specification and verification. Thus, think of `vlen` as the *actual*
size of a `Vector` (regardless of how that was computed).

\newthought{Assumes} are used to *specify* types describing the semantics of
functions that we cannot verify e.g. because we don't have the code
for them. Here, we are assuming that the library function `Data.Vector.length`
indeed computes the size of the input vector. Furthermore, we are stipulating
that the lookup function `(!)` requires an index that is betwen `0` and the real
size of the input vector `x`.

\newthought{Dependent Refinements} are used to describe relationships
*between* the elements of a specification. For example, notice how the
signature for `length` names the input with the binder `x` that then
appears in the output type to constrain the output `Int`. Similarly,
the signature for `(!)` names the input vector `x` so that the index
can be constrained to be valid for `x`.  Thus dependency is essential
for writing properties that connect different program values.

\newthought{Aliases} are extremely useful for defining shorthands for
commonly occuring types. Just as we enjoy abstractions when programming,
we will find it handy to have abstractions in the specification mechanism.
To this end, LiquidHaskell supports *type aliases*. For example, we can
define `Vector`s of a given size `N` as:

\begin{code}
{-@ type VectorN a N = {v:Vector a | vlen v == N} @-}
\end{code}

and now use this to type `twoLangs` above as:

\begin{code}
{-@ twoLangs  :: VectorN String 2 @-}
\end{code}

Similarly, we can define an alias for `Int` values between `Lo` and `Hi`:

\begin{code}
{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}
\end{code}

\noindent
after which we can specify `(!)` as:

\begin{spec}
(!) :: x:Vector a -> Btwn 0 (vlen x) -> a
\end{spec}

Verification: Vector Lookup
---------------------------

Lets try write some simple functions to sanity check the above specifications. 

First, consider a function that returns the starting element of a `Vector`:

\begin{code}
startElem     :: Vector a -> a
startElem vec = vec ! 0
\end{code}

When we check the above, we get an error:

\begin{liquiderror}
     src/03-poly.lhs:127:23: Error: Liquid Type Mismatch
       Inferred type
         VV : Int | VV == ?a && VV == (0  :  int)
      
       not a subtype of Required type
         VV : Int | VV >= 0 && VV < vlen vec
      
       In Context
         VV  : Int | VV == ?a && VV == (0  :  int)
         vec : (Vector a) | 0 <= vlen vec
         ?a  : Int | ?a == (0  :  int)
\end{liquiderror}

Intuitively LH is saying that `0` is *not* a valid index because it is not
between `0` and `vlen vec`. Say what? Well, what if `vec` had *no* elements!

Ah, of course. A formal verifier doesn't make *off by one* errors (thankfully!)

We can fix the problem in one of two ways:

1. *Require* that the input `vec` be non-empty.
2. *Return* an output if `vec` is non-empty, or

Here's an implementation of the first approach, where we require the input
to be non-empty.

\begin{code}
{-@ startElem' :: VectorNE a -> a @-}
startElem' vec = vec ! 0
\end{code}

where `VectorNE` describes non-empty `Vector`s:

\begin{code}
{-@ type VectorNE a = {v:Vector a | 0 < vlen v} @-}
\end{code}

\exercise Replace the `undefined` with an *implementation* of `startElem''`
which accepts *all* `Vector`s but returns a value only when the input `vec`
is not empty. 

\begin{code}
startElem''     :: Vector a -> Maybe a 
startElem'' vec = undefined
\end{code}

\exercise Consider `unsafeLookup` which is essentially a wrapper around the `(!)`
with the arguments flipped:

\begin{code}
{-@ unsafeLookup :: Int -> Vector a -> a @-}
unsafeLookup index vec = vec ! index
\end{code}

Modify the *specification* for `unsafeLookup` (i.e. the text between `{-@ ... @-}`)
to make the *implementation* typecheck.

\exercise Write a `safeLookup` function that fills in the implementation of `ok`
to performs a *bounds check* before looking up the vector.

\begin{code}
{-@ safeLookup :: Vector a -> Int -> Maybe a @-}
safeLookup x i 
  | ok        = Just (x ! i)
  | otherwise = Nothing 
  where
    ok        = undefined
\end{code}

Verification: Our First Recursive Function
------------------------------------------

Ok, lets write some code! Lets start with a recursive
function that adds up the values of the elements of an
`Int` vector.

\begin{code}
-- >>> vectorSum (fromList [1, -2, 3])
-- 2 
vectorSum         :: Vector Int -> Int 
vectorSum vec     = go 0 0
  where
    go acc i 
      | i < sz    = go (acc + (vec ! i)) (i + 1)
      | otherwise = acc 
    sz            = length vec
\end{code}

\exercise What happens if you *replace* the guard with `i <= sz`?

\exercise Write a variant of the above function that computes the
 `absoluteSum` of the elements of the vector.

\begin{code}
-- >>> absoluteSum (fromList [1, -2, 3])
-- 6
{-@ absoluteSum :: Vector Int -> Nat @-}
absoluteSum     :: Vector Int -> Int
absoluteSum     = undefined
\end{code}


Refinement Inference
--------------------

LiquidHaskell verifies `vectorSum` -- or, to be precise, the safety of
the vector accesses `vec ! i`.  The verification works out because
LiquidHaskell is able to *automatically infer* \footnotetext{In your editor, click on `go` to see the inferred type.}

\begin{spec}
go :: Int -> {v:Int | v >= 0 && v <= sz} -> Int
\end{spec}

\noindent which states that the second parameter `i` is
between `0` and the length of `vec` (inclusive). LiquidHaskell
uses these and the test that `i < sz` to establish that `i` is
in fact between `0` and `(vlen vec)` thereby verifing safety. 

\exercise Why does `go`'s type have `v <= sz` instead of `v < sz` ?


Higher-Order Functions: Bottling Recursion in a `loop`
------------------------------------------------------

Lets refactor the above low-level recursive function 
into a generic higher-order `loop`.

\begin{code}
loop :: Int -> Int -> a -> (Int -> a -> a) -> a 
loop lo hi base f =  go base lo
  where
    go acc i     
      | i < hi    = go (f i acc) (i + 1)
      | otherwise = acc
\end{code}

We can now use `loop` to implement `vectorSum`:

\begin{code}
vectorSum'      :: Vector Int -> Int 
vectorSum' vec  = loop 0 n 0 body
  where
    body i acc  = acc + (vec ! i)
    n           = length vec
\end{code}

\newthought{Inference} is a convenient option. LiquidHaskell finds:

\begin{spec}
loop :: lo:Nat -> hi:{Nat | lo <= hi} -> a -> (Btwn lo hi -> a -> a) -> a
\end{spec}

\noindent In english, the above type states that 

- `lo` the loop *lower* bound is a non-negative integer
- `hi` the loop *upper* bound is a greater than `lo`,
- `f`  the loop *body* is only called with integers between `lo` and `hi`.

\noindent
It can be tedious to have to keep typing things like the above.
If we wanted to make `loop` a public or exported function, we
could use the inferred type to generate an explicit signature.

At the call `loop 0 n 0 body` the parameters `lo` and `hi` are
instantiated with `0` and `n` respectively (which, by the way
is where the inference engine deduces non-negativity from) and
thus LiquidHaskell concludes that `body` is only called with
values of `i` that are *between* `0` and `(vlen vec)`, which
shows the safety of the call `vec ! i`.

\exercise Complete the implementation of `absoluteSum'` below.
When you are done, what is the type that is inferred for `body`?

\begin{code}
-- >>> absoluteSum' (fromList [1, -2, 3])
-- 6
{-@ absoluteSum' :: Vector Int -> Nat @-}
absoluteSum'     :: Vector Int -> Int
absoluteSum' vec = loop 0 n 0 body
  where
    n            = length vec
    body i acc   = undefined
\end{code}

\exercise Lets use `loop` to compute `dotProduct`s:

\begin{code}
-- >>> dotProduct (fromList [1,2,3]) (fromList [4,5,6])
-- 32 
{-@ dotProduct :: x:Vector Int -> y:Vector Int -> Int @-}
dotProduct     :: Vector Int -> Vector Int -> Int
dotProduct x y = loop 0 sz 0 body 
  where
    sz         = length x
    body i acc = acc + (x ! i)  *  (y ! i)
\end{code}

\noindent Why does LiquidHaskell flag an error in the above?
Fix the code or specification to get a correct `dotProduct`.

Refining Data Types: Sparse Vectors
-----------------------------------

While the standard `Vector` is great for *dense* arrays,
often we have to manipulate *sparse* vectors where most
elements are just `0`. We might represent such vectors
as a list of index-value tuples:

\begin{code}
{-@ type SparseN a N = [(Btwn 0 N, a)] @-}
\end{code}

\noindent Implicitly, all indices *other* than those in the list
have the value `0` (or the equivalent value for the type `a`).

\newthought{Alias} `SparseN` is just a 
shorthand for the (longer) type on the right, it does not
*define* a new type. If you are familiar with the *index-style*
length encoding e.g. as found in [DML][dml] or [Agda][agdavec],
then note that despite  appearances, our `Sparse` definition
is *not* indexed.

\newthought{Sparse Products}
Lets write a function to compute a sparse product

\begin{code}
{-@ sparseProduct        :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
sparseProduct x y        = go 0 y
  where 
    go sum ((i, v) : y') = go (sum + (x ! i) *  v) y' 
    go sum []            = sum
\end{code}

LiquidHaskell verifies the above by using the specification
to conclude that for each tuple `(i, v)` in the list `y`, the
value of `i` is within the bounds of the vector `x`, thereby
proving `x ! i` safe.

Refinements and Polymorphism
----------------------------

The sharp reader will have undoubtedly noticed that the sparse product 
can be more cleanly expressed as a [fold][foldl]:

\begin{spec}
foldl' :: (a -> b -> a) -> a -> [b] -> a
\end{spec}

\noindent We can simply fold over the sparse vector, accumulating the `sum`
as we go along

\begin{code}
{-@ sparseProduct'  :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
sparseProduct' x y  = foldl' body 0 y   
  where 
    body sum (i, v) = sum + (x ! i)  * v
\end{code}

\noindent
LiquidHaskell digests this too, without much difficulty. 
The main trick is in how the polymorphism of `foldl'` is instantiated. 

1. The GHC type inference engine deduces that at this site,
   the type variable `b` from the signature of `foldl'` is
   instantiated to the Haskell type `(Int, a)`. 

2. Correspondingly, LiquidHaskell infers that in fact `b`
   can be instantiated to the *refined* `(Btwn 0 v (vlen x), a)`. 

Thus, the inference mechanism saves us a fair bit of typing and allows us to
reuse existing polymorphic functions over containers and such without ceremony.

\newthought{Thats all} for now! Hopefully the above gives you
a reasonable idea of how one can use refinements to verify size
related properties, and more generally, to specify and verify
properties of recursive, and polymorphic functions operating
over datatypes. Read on to learn how we can teach LiquidHaskell
to reason about *structural* properties of data types.

[vecspec]:  https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/Data/Vector.spec
[vec]:      http://hackage.haskell.org/package/vector
[dml]:      http://www.cs.bu.edu/~hwxi/DML/DML.html
[agdavec]:  http://code.haskell.org/Agda/examples/Vec.agda
[ref101]:   /blog/2013/01/01/refinement-types-101.lhs/ 
[ref102]:   /blog/2013/01/27/refinements-101-reax.lhs/ 
[foldl]:    http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html
[listtail]: /blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/
[dmlarray]: http://www.cs.bu.edu/~hwxi/academic/papers/pldi98.pdf

