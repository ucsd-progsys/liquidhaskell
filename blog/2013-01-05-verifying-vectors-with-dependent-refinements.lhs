
---
layout: post
title: "Verifying Vectors With Dependent Refinements"
date: 2013-01-05 16:12
author: Ranjit Jhala
published: true 
comments: true
external-url:
categories: basic
---


Hopefully, the [previous][ref101] article gave you a basic idea about what
refinement types look like. Today, lets build on that intuition with some 
small examples that illustrate how LiquidHaskell can be used to do 
compile-time **bounds checking**, while reasoning about 

- *recursion*
- *higher-order functions*
- *data types*, and 
- *polymorphism*.

<!-- more -->

\begin{code}
module DependentRefinements (
    safeLookup , unsafeLookup
  , absoluteSum, absoluteSum'
  , dotProduct
  ) where

import Data.List    (foldl')
import Data.Vector 
\end{code}

Specifying Bounds for Vectors
-----------------------------

One [classical][dml] use-case 
for refinement types is to verify the safety of accesses of arrays 
and vectors and such, by proving that the indices used in such accesses 
are *within bounds*. In this article, we will develop the above ideas 
by writing a few short functions that manipulate vectors, such as those
from the popular [vector][vec] library.

We can **specify** bounds safety by writing refined versions of the 
types for the [key functions][vecspec] exported by the module `Data.Vector`. 

``` haskell Partial Specifications for `Data.Vector` https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/Data/Vector.spec
module spec Data.Vector where

import GHC.Base

measure vlen    ::   (Vector a) -> Int 
assume length   :: x:(Vector a) -> {v : Int | v = (vlen x)}
assume !        :: x:(Vector a) -> {v : Int | ((0 <= v) && (v < (vlen x))) } -> a 
```

In particular, we 

- **define** a *property* called `vlen` which denotes the size of the vector,
- **assume** that the `length` function *returns* an integer equal to the vector's size, and
- **assume** that the lookup function `!` *requires* an index between `0` and the vector's size.

There are several things worth paying close attention to in the above snippet.

#### Measures

Measures define auxiliary (or so-called **ghost**) properties of data
values that are useful for specification and verification, but which 
*don't actually exist at run-time*. Thus, they will *only appear in specifications*,
i.e. inside type refinements, but *never* inside code. Often we will use
helper functions like `length` in this case, which "pull" (reify?) 
the ghost values from the refinement world into the actual code world.

#### Assumes 

We write `assume` because in this scenario we are *not verifying* the
implementation of `Data.Vector`, we are simply *using* the properties of
the library to verify client code.  If we wanted to verify the library
itself, we would ascribe the above types to the relevant functions in the
Haskell source for `Data.Vector`. 

#### Dependent Refinements

Notice that in the function type (e.g. for `length`) we have *named* the *input*
parameter `x` so that we can refer to it in the *output* refinement. In this case, 
the type 

``` haskell 
assume length   :: x:(Vector a) -> {v : Int | v = (vlen x)}
```

states that the `Int` output is exactly equal to the number of elements in 
the input `Vector` (named) `x`.

In other words, the output refinement **depends on** the input value, which
crucially allows us to write properties that *relate* different program values.

#### Verifying a Simple Wrapper

Lets try write some simple functions to sanity check the above specifications. 
First, consider an *unsafe* vector lookup function:

\begin{code}
unsafeLookup vec index = vec ! index
\end{code}

If we run this through LiquidHaskell, it will spit back a type error for
the expression `x ! i` because (happily!) it cannot prove that `index` is
between `0` and the `vlen vec`. Of course, we can specify the bounds 
requirement in the input type

\begin{code}
{-@ unsafeLookup :: vec:Vector a -> {v: Int | (0 <= v && v < (vlen vec)) } -> a @-}
\end{code}

then LiquidHaskell is happy to verify the lookup. Of course, now the burden
of ensuring the index is valid is pushed to clients of `unsafeLookup`.

Instead, we might write a *safe* lookup function that performs the *bounds check*
before looking up the vector:

\begin{code}
safeLookup x i 
  | 0 <= i && i < length x = Just (x ! i)
  | otherwise              = Nothing 
\end{code}

#### Predicate Aliases

The type for `unsafeLookup` above is rather verbose as we have to spell out
the upper and lower bounds and conjoin them. Just as we enjoy abstractions
when programming, we will find it handy to have abstractions in the
specification mechanism. 

To this end, LiquidHaskell supports *predicate aliases*, which, 
(like everything else!) are best illustrated by example

\begin{code}
{-@ predicate Btwn lo i hi = ((lo <= i) && (i < hi)) @-}
{-@ predicate InBounds i a = (Btwn 0 i (vlen a))     @-}
\end{code}

Now, we can simplify (the type for) the unsafe lookup function to

\begin{code}
{-@ unsafeLookup' :: vec:Vector a -> {v: Int | (InBounds v vec)} -> a @-}
unsafeLookup' vec i = vec ! i
\end{code}


Our First Recursive Function
----------------------------

OK, with the tedious preliminaries out of the way, lets write some code!

To start: a vanilla recursive function that adds up the absolute values of
the elements of an integer vector.

\begin{code}
absoluteSum       :: Vector Int -> Int 
absoluteSum vec   = if 0 < n then go 0 0 else 0
  where
    go acc i 
      | i /= n    = go (acc + abz (vec ! i)) (i + 1)
      | otherwise = acc 
    n             = length vec
\end{code}

where the function `abz` is the absolute value function from [before][ref101].

\begin{code}
abz n = if 0 <= n then n else (0 - n) 
\end{code}

Digression: Introducing Errors  
------------------------------

If you are following along in the demo page -- I heartily 
recommend that you try the following *(cough)* modifications, 
one at a time, and see what happens.

**What happens if:** 
- You *remove* the check `0 < n` 
- You *replace* the guard with `i <= n`

In each case, LiquidHaskell will grumble that your program is *unsafe*. 
Do you understand why?

Refinement Type Inference
-------------------------

LiquidHaskell happily verifies `absoluteSum` -- to be precise, 
the vector accesses `vec ! i`. 

The verification works out because LiquidHaskell is able **automatically**
infer a suitable type for `go`. Shuffle your mouse over the identifier 
above to see the inferred type. Observe that the type states that
The first parameter `acc` (and the output) is `0 <= V`. 
That is, the returned value is non-negative.

More importantly, the type states that the second parameter `i` is 
`0 <= V` and `V <= n` and `V <= (vlen vec)`. That is, the parameter `i` 
is between `0` and the vector length (inclusive). LiquidHaskell uses these 
and the test that `i /= n` to establish that `i` is in fact between `0` 
and `(vlen vec)` thereby verifing safety. 

In fact, if we want to use the function externally (i.e. in another module) 
we can go ahead and strengthen its type to specify that the output is 
non-negative.

\begin{code}
{-@ absoluteSum :: Vector Int -> {v: Int | 0 <= v}  @-} 
\end{code}

**What happens if:** You *replace* the output type with `{v: Int | 0 < v }` ?

Bottling Recursion With a Higher-Order `loop`
---------------------------------------------

Next, lets refactor the above low-level recursive function 
into a generic higher-order `loop`.

\begin{code}
loop :: Int -> Int -> a -> (Int -> a -> a) -> a 
loop lo hi base f = go base lo
  where
    go acc i     
      | i /= n    = go (f i acc) (i + 1)
      | otherwise = acc
\end{code}

### Using `loop` to compute `absoluteSum`

We can now use `loop` to implement `absoluteSum` like so:

\begin{code}
absoluteSum' vec = if 0 < n then loop 0 n 0 body else 0
  where body     = \i acc -> acc + (vec ! i)
        n        = length vec
\end{code}

LiquidHaskell verifies `absoluteSum'` without any trouble.

It is very instructive to see the type that LiquidHaskell *infers* 
for `loop` -- it looks something like

\begin{code}
{-@ loop :: lo: {v: Int | (0 <= v) }  
         -> hi: {v: Int | ((0 <= v) && (lo <= v))} 
         -> a 
         -> (i: {v: Int | (Btwn lo v hi)} -> a -> a)
         -> a 
  @-}
\end{code}

In english, the above type states that 

- `lo` the loop *lower* bound is a non-negative integer
- `hi` the loop *upper* bound is a greater than `lo`,
- `f`  the loop *body* is only called with integers between `lo` and `hi`.

Inference is a rather convenient option -- it can be tedious to have to keep 
typing things like the above! Of course, if we wanted to make `loop` a
public or exported function, we could use the inferred type to write (or
generate) an explicit signature too.

At the call 

```haskell
loop 0 n 0 body 
```

the parameters `lo` and `hi` are instantiated with `0` and `n` respectively
(which, by the way is where the inference engine deduces non-negativity
from) and thus LiquidHaskell concludes that `body` is only called with
values of `i` that are *between* `0` and `(vlen vec)`, which shows the 
safety of the call `vec ! i`.

### Using `loop` to compute `dotProduct`

Here's another use of `loop` -- this time to compute the `dotProduct` 
of two vectors. 

\begin{code}
dotProduct     :: Vector Int -> Vector Int -> Int
dotProduct x y = loop 0 (vlen x) 0 (\i -> (+ (x ! i) * (y ! i))) 
\end{code}

The gimlet-eyed reader will realize that the above is quite unsafe -- what
if `x` is a 10-dimensional vector while `y` has only 3-dimensions? A nasty:

```haskell
*** Exception: ./Data/Vector/Generic.hs:244 ((!)): index out of bounds ...
```

*Yech*. 

This is precisely the sort of nasty surprise we want to do away with at 
compile-time. Refinements to the rescue! We can specify that the vectors 
have the same dimensions quite easily

\begin{code}
{-@ dotProduct :: x:(Vector Int) 
               -> y:{v: (Vector Int) | (vlen v) = (vlen x)} 
               -> Int 
  @-}
\end{code}

after which LiquidHaskell will gladly verify that the implementation of
`dotProduct` is indeed safe!

Refining Data Types
-------------------

Next, suppose we want to write a **sparse** dot product function. 
That is, a dot product between a vector and a second *sparse vector* 
that is represented by a list of index-value tuples.

#### Representing Sparse Vectors

We can represent the sparse vector with a **refinement type alias** 

{-@ type SparseVector a n = [({v: Int | (Btwn 0 v n)}, a)] @-}

As with usual types, an alias is just a shorthand for the longer type 
on the right, it does not actually define a new type. Thus, the above 
alias is simply a refinement of Haskell's `[(Int, a)]` type, with a 
size parameter `n` that facilitates ease reuse. Thus, refinements let
us express invariants of containers in a straightforward manner. 

**Aside:** It is worth reminding readers who might be familiar 
with *indexed-style* length encoding e.g. as found in [DML][dml] 
or [Agda][agdavec], that despite appearances, our `SparseVector` 
definition is *not* indexed. Instead, we deliberately choose to
encode properties with logical refinement predicates, to 
facilitate SMT based checking and inference.

#### Verifying Uses of Sparse Vectors

Next, we can write a recursive procedure that computes the sparse product

{-@ sparseDotProduct :: (Num a) => x:(Vector a) -> SparseVector a (vlen x) -> a @-}
sparseDotProduct x y  = go 0 y
  where 
    go sum ((i, v) : y') = go (sum + (x ! i) * v) y' 
    go sum []            = sum

LiquidHaskell verifies the above by using the specification for `y` to
conclude that for each tuple `(i, v)` in the list, the value of `i` is 
within the bounds of the vector `x`, thereby proving the safety of the 
access `x ! i`.

Refinements and Polymorphism
----------------------------

The sharp reader will have undoubtedly noticed that the sparse product 
can be more cleanly expressed as a [left fold][foldl]. Indeed, let us 
recall the type of the `foldl` operation

```haskell
foldl' :: (a -> b -> a) -> a -> [b] -> a
```

Thus, we can simply fold over the sparse vector, accumulating the `sum`
as we go along

\begin{code}
{-@ sparseDotProduct' :: (Num a) => x:(Vector a) -> SparseVector a (vlen x) -> a @-}
sparseDotProduct' x y   = foldl' body 0 y   
  where body sum (i, v) = sum + (x ! i) * v
\end{code}

LiquidHaskell digests this too, without much difficulty. 

The main trick is in how the polymorphism of `foldl'` is instantiated. 
The GHC type inference engine deduces, that at this site, the type variable
`b` from the signature of `foldl'` is instantiated to the Haskell type `(Int, a)`. 

Correspondingly, LiquidHaskell infers that in fact `b` can be instantiated
to the *refined* type `({v: Int | (Btwn 0 v (vlen x))}, a)`. Walk the mouse 
over to `i` to see this inferred type. (You can also hover over `foldl'`above
to see the rather more verbose fully instantiated type.)

Thus, the inference mechanism saves us a fair bit of typing and allows us to
reuse existing polymorphic functions over containers and such without any 
ceremony.

Conclusion
----------

Thats all for now folks! Hopefully the above gives you a reasonable idea of
how one can use refinements to verify size related properties, and more
generally, to specify and verify properties of recursive, and polymorphic
functions operating over datatypes. Next time, we'll look at how we can
teach LiquidHaskell to think about properties of recursive structures
like lists and trees.

[vecspec]: https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/Data/Vector.spec
[vec]:     http://hackage.haskell.org/package/vector
[dml]:     http://www.cs.bu.edu/~hwxi/DML/DML.html
[agdavec]: http://code.haskell.org/Agda/examples/Vec.agda
[ref101]:  /blog/2012/12/20/refinement-types-101.lhs/ "Refinement Types 101"
[foldl]:   http://hackage.haskell.org/packages/archive/base/latest/doc/html/src/Data-List.html#foldl%27



