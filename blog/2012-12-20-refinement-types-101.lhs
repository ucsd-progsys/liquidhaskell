---
layout: post
title: "Refinement Types 101"
date: 2012-12-20 16:12
author: Ranjit Jhala
published: true
comments: true
external-url:
categories: basic
---

One of the great things about Haskell, is its brainy type system that
allows one to enforce a variety of invariants at compile time, thereby
nipping in the bud, a large swathe of run-time errors. Refinement types
allow us to use modern logic solvers (*aka* SAT and SMT engines) to
dramatically extend the scope of invariants that can be statically
verified.

What is a Refinement Type?
--------------------------

In a nutshell, 

<blockquote><p>
Refinement Types = Types + Logical Predicates
</p></blockquote>

That is, refinement types allow us to decorate types with 
*logical predicates* which constrain the set of values described
by the type, and hence, allow us to specify sophisticated invariants 
of the underlying values.

Say what? 

<!-- more -->

\begin{code}
module Intro where

import Language.Haskell.Liquid.Prelude  (liquidAssert)
\end{code}

Let us jump right in with a simple example, the number `0 :: Int`. 
As far as Haskell is concerned, the number is simply an `Int` (lets not
worry about things like `Num` for the moment.) So are, `2` and `7` and 
`904`. With refinements, we can dress up these values so that they 
stand apart. For example, consider the binder

\begin{code}
zero' :: Int
zero' = 0
\end{code}

We can ascribe to the variable `zero'` the refinement type

\begin{code}
{-@ zero' :: {v: Int | 0 <= v} @-}
\end{code}

which is simply the basic type `Int` dressed up with a predicate.
The binder `v` is called the *value variable*, and so the above denotes 
the set of `Int` values which are greater than `0`. Of course, we can
attach other predicates to the above value, for example

\begin{code}
{-@ zero'' :: {v: Int | ((0 <= v) && (v < 100)) } @-}
zero'' :: Int
zero'' = 0
\end{code}

which states that the number is in the range `0` to `100`, or

\begin{code}
{-@ zero''' :: {v: Int | (v mod 2) = 0} @-}
zero''' :: Int
zero''' = 0
\end{code}

where `mod` is the *modulus* operator in the refinement logic. Thus, the type
above states that zero is an *even* number.

We can also use a singleton type that precisely describes the constant

\begin{code}
{-@ zero'''' :: {v: Int | v = 0 } @-}
zero'''' :: Int
zero'''' = 0
\end{code}

(Aside: we use a different names `zero'`, `zero''` etc. for a silly technical 
reason -- LiquidHaskell requires that we ascribe a single refinement type to 
a top-level name.)

Finally, we could write a single type that captures all the properties above:

\begin{code}
{-@ zero :: {v: Int | ((0 <= v) && ((v mod 2) = 0)) } @-}
zero     :: Int
zero     =  0
\end{code}

The key points are:

1. a refinement type is just a type *decorated* with logical predicates,
2. a value can have *different* refinement types that describe different properties.
3. if we *erase* the green bits (i.e. the logical predicates) we get back *exactly* 
   the usual Haskell types that we know and love.

We have built a refinement type based verifier called LiquidHaskell. 
Lets see how we can use refinement types to specify and verify interesting 
program invariants in LiquidHaskell.

Writing Safety Specifications
-----------------------------

We can use refinement types to write various kinds of more interesting
safety specifications.

First, we can write a wrapper around the usual `error` function 

\begin{code}
{-@ error' :: {v: String | false } -> a  @-}
error'     :: String -> a
error'     = error
\end{code}

The interesting thing about the type signature for `error'` is that the
input type has the refinement `false`. That is, the function must only be
called with `String`s that satisfy the predicate `false`. Of course, there
are *no* such values. Thus, a program containing the above function
typechecks *exactly* when LiquidHaskell can prove that the function
`error'` is *never called*.

Next, we can use refinements to encode arbitrary programmer-specified 
**assertions** by defining a function

\begin{code}
{-@ lAssert     :: {v:Bool | (? v)} -> a -> a  @-}
lAssert         :: Bool -> a -> a 
lAssert True  x = x
lAssert False _ = error' "lAssert failure" 
\end{code}

The input type for this function specifies that the function must *only* be 
called with `True` values (the syntax `? v` means `v` interpreted as a
proposition.)


Refining Function Types : Preconditions
---------------------------------------

Lets use the above to write a *divide* function that *only accepts* non-zero
denominators. 

\begin{code}
divide     :: Int -> Int -> Int
divide n 0 = error' "divide by zero"
divide n d = n `div` d
\end{code}

We can specify that the non-zero denominator *precondition* with a suitable 
refinement on the *input* component of the function's type 

\begin{code}
{-@ divide :: Int -> {v: Int | v != 0 } -> Int @-}
\end{code}

To typecheck the `divide` function, LiquidHaskell verifies that `"divide by zero"` 
is a subtype of `{v:String | false}` at the call to `error'`. LiquidHaskell
does so by using the fact that (in the pertinent equation) the denominator 
parameter is in fact `0 :: {v: Int | v = 0}` which *contradicts* the
precondition.
In other words, LiquidHaskell deduces by contradiction, that the first equation 
is *dead code* and hence `error'` will not be called at run-time.

If you are paranoid, you can put in an explicit assertion

\begin{code}
divide'     :: Int -> Int -> Int
divide' n 0 = error' "divide by zero"
divide' n d = lAssert (d /= 0) $ n `div` d
\end{code}

and LiquidHaskell will verify the assertion (by verifying the call to
`lAssert`) for you.

Refining Function Types : Postconditions
----------------------------------------

Next, lets see how we can use refinements to describe the *outputs* of a
function. Consider the following simple *absolute value* function

\begin{code}
abz               :: Int -> Int
abz n | 0 < n     = n
      | otherwise = 0 - n
\end{code}

We can use a refinement on the output type to specify that the function 
returns non-negative values

\begin{code}
{-@ abz :: Int -> {v: Int | 0 <= v } @-}
\end{code}

LiquidHaskell *verifies* that `abz` indeed enjoys the above type by
deducing that `n` is trivially non-negative when `0 < n` and that in 
the `otherwise` case, i.e. when `not (0 < n)`, the value `0 - n` is in
indeed non-negative (lets not worry about underflows for the moment.)

Putting It All Together: A `truncate` function
----------------------------------------------

Lets wrap up this introduction with a simple `truncate` function 
that connects all the dots. 

\begin{code}
{-@ truncate :: Int -> Int -> Int @-}
truncate i max  
  | i' <= max' = i
  | otherwise  = max' * (i `divide` i')
    where i'   = abz i
          max' = abz max 
\end{code}

`truncate i n` simply returns `i` if its absolute value is less the
upper bound `max`, and otherwise, *truncates* the value at the maximum.
LiquidHaskell verifies that the use of `divide` is safe by inferring that 
at the callsite, 

1. `i' > max'` from the branch condition,
2. `0 <= i'`   from the `abz` postcondition (hover mouse over `i'`)
3. `0 <= max'` from the `abz` postcondition (hover mouse over `max'`)

From the above, LiquidHaskell infers that `i' != 0`. That is, at the
callsite, the argument `i' :: {v: Int | v != 0}` thereby satisfying the
precondition for `divide`, thus verifying that the program has no pesky 
divide-by-zero errors. Again, if you are *really* want to make sure, put 
in an assertion

\begin{code}
{-@ truncate' :: Int -> Int -> Int @-}
truncate' i max  
  | i' <= max' = i
  | otherwise  = lAssert (i' /= 0) $ max' * (i `divide` i')
    where i'   = abz i
          max' = abz max 
\end{code}

and *lo!* LiquidHaskell will verify it for you.

Modular Verification
--------------------

Incidentally, note the `import` statement at the top. Rather than rolling
our own `lAssert` we can import and use a pre-defined version `liquidAssert` 
defined in an external [module](https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/Language/Haskell/Liquid/Prelude.hs)

\begin{code}
{-@ truncate'' :: Int -> Int -> Int @-}
truncate'' i max  
  | i' <= max' = i
  | otherwise  = liquidAssert (i' /= 0) $ max' * (i `divide` i')
    where i'   = abz i
          max' = abz max 
\end{code}

In fact, LiquidHaskell comes equipped with suitable refinements for
standard functions, and it is easy to add refinements as we shall
demonstrate in subsequent articles.

Take Away Lessons
-----------------

This concludes our quick introduction to Refinement Types and
LiquidHaskell. Hopefully you have learnt how to

1. *Specify* fine-grained properties of values by decorating their
   types with logical predicates,
2. *Encode* assertions, preconditions and postconditions with suitable
   function types,
3. *Verify* semantic properties of code by using automatic logic engines 
   (SMT solvers) to track and establish the key relationships between 
   program values.


