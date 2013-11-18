---
layout: post
title: "Termination Checking"
date: 2013-11-18 16:12
comments: true
external-url:
categories: termination
author: Niki Vazou
published: true
demo: TerminationBasic.hs
---

If you used liquidHaskell lately, you may have noticed some type errors that
just make no sense.
Well, that is not a bug, but a ... **termination checker** failing to prove that
your function terminates.
In this post, we present how you can use liquidHaskell to prove termination on
simple recursive functions.

<!-- more -->

\begin{code}
module Termination where

import Prelude hiding (sum, (!!))
import Data.List      (lookup)
\end{code}

Termination Check with Refinement Types
---------------------------------------

Consider a `Vec`tor that maps `Int`egers to `Val`ues:

\begin{code}
type Val   = Int
data Vec   = V [(Int, Val)]

(!!)       :: Vec -> Int -> Val
(V a) !! i = case i `lookup` a of {Just v -> v; _ -> 0}
\end{code}

Let `sum a i` add the `i` first elements of the vector `a`:

\begin{code}
sum     :: Vec -> Int -> Val
sum a 0 = 0
sum a i = (a !! (i-1)) + sum a (i-1)
\end{code}

Does `sum` terminate?
We observe that if `i` is not `0` then `sum i` will call `sum (i-1)`, otherwise
it will return.
This reasoning suffices to convince ourselves that `sum i` terminates for every
natural number `i`.
Formally, we shown that `sum` terminates because a *well-founded metric* (i.e., the
natural number `i`) is decreasing at each iteration.
Thus, to ensure termination it suffices to restrict `i` on Natural numbers,
which we can do with a liquid-type signature.
\begin{code}
{-@ sum :: Vec -> Nat -> Val @-}
\end{code}

LiquidHaskell will apply the same reasoning to prove `sum`
terminates:
Conventionally, to typecheck `sum` we would check the body assuming an
environment

`a:Vec`, `i:Nat`, `sum:Vec -> Nat -> Val`

Instead, we *weaken* the environment to 

`a:Vec`, `i:Nat`, `sum:Vec -> {v:Nat| v < i} -> Val`

Now, the type of `sum` stipulates that it *only* be recursively called with
`Nat` (so well-founded) values that are *strictly less than* the current parameter `i`. 
Since its body typechecks in this environment, `sum` terminates for
every `i` on `Nat`s.

Choosing the correct argument
-----------------------------

We saw that liquidHaskell can happily check that a Natural number is decreasing
at each iteration; but it uses a na&#239;ve heuristic to choose which one. 
For this post we can assume that it always chooses *the first* Integer. 

So, a tail-recursive implementation of `sum`:
\begin{code}
{-@ sum' :: Vec -> Val -> Nat -> Val @-}
sum' :: Vec -> Val -> Int -> Val
sum' a acc 0 = acc + a!!0 
sum' a acc i = sum' a (acc + a!!i) (i-1)
\end{code}

will fail, as liquidHaskell wants to prove that the `acc`umulator is the `Nat`ural
number that
decreases at each iteration.

\begin{code}The remedy is simple. We can direct liquidHaskell to the correct argument `i` using a `Decrease` annotation: 
{-@ Decrease sum' 3 @-}
\end{code}
which directs liquidHaskell to check whether the *third*
argument (i.e., `i`) is decreasing.
With this hint, liquidHaskell will happily verify that `sum'` is indeed a
terminating function.


Lexicographic Termination
-------------------------

Lets complicate the things a little bit.
To do so, lets compute the `sum` of a 2D `Vec`tor:

\begin{code}
data Vec2D    = V2D [((Int, Int), Val)]

(!!!)         :: Vec2D -> (Int,Int) -> Val
(V2D a) !!! i = case i `lookup` a of {Just v -> v; _ -> 0}
\end{code}

Now we write a `sum2D a n m` function that computes the sum of the first 
`(n+1)(m+1)` elements of `a`

\begin{code}
{-@ sum2D :: Vec2D -> Nat -> Nat -> Val @-}
sum2D :: Vec2D -> Int -> Int -> Val
sum2D a n m = go n m
  where 
       {-@ Decrease go 1 2 @-}
        go 0 0             = 0
        go i j | j == 0    =  a!!!(i, 0) + go (i-1) m
               | otherwise =  a!!!(i, j) + go i (j-1)
\end{code}

Here there is no decreasing argument, 
if `j>0`, `j` decreases (line `139`), otherwise `i` decreases (line `138`).
Though, liquidHaskell succeed in verifying that `sum2D` terminates and the reason
is our `Decrease go 1 2` annotation.
This annotation informs the tool that the decreasing measure is the
*lexicographically ordered* pair `[i,j]`. 
LiquidHaskell will verify that this pair is indeed decreasing: at each
iteration either `i` decreases (line `138`) or `i` remains the same and `j`
decreases (line `139`).

\begin{code}An alternative annotation to express the above decreasing measure is:
       {-@ go :: i:Nat -> j:Nat -> Val / [i, j] @-}
\end{code}
where after the type signature for `go` we write the list of lexicographic
decreasing *expressions*.
This mechanism, as we shall see, allows us to prove termination in functions
where the decreasing measure in a *function* of the arguments.

Decreasing expressions
----------------------
Back to our `1D` Vector, 
we now define a function `sumFromTo a lo hi` that sums the elements form `a!!lo`
to `a!!hi`:

\begin{code}
{-@ sumFromTo :: Vec -> lo:Nat -> hi:{v:Nat|v>=lo} -> Val @-}
sumFromTo :: Vec -> Int -> Int ->  Val
sumFromTo a lo hi = go lo hi
  where 
       {-@ go :: lo:Nat -> hi:{v:Nat|v>=lo} -> Val / [hi-lo] @-}
        go lo hi | lo == hi  =  a!!lo
                 | otherwise =  a!!lo + go (lo+1) hi
\end{code}

No argument is decreasing in this function, 
but still it does terminate, as at each iteration `lo` is increased and
execution will terminate when `lo` reaches `hi`.
Here the decreasing measure is the expression `hi-lo`.
LiquidHaskell has no way to generate such a measure, but,
if the user generates it, i.e., by annotating `go`'s signature,
liquidHaskell will happily check that `lo-hi` is indeed a well-founded measure (as it is
a natural number) that decreases at each iteration.


Powered with decreasing expressions and the `Decrease` hint,
we can prove termination on a great number of functions 
ranging from 
ones defined on recursive data structures
to mutual recursive ones. 
We shall soon see how to prove termination on more complicated functions, why
is termination analysis required by liquidHaskell and when is it safe to
deactivate it.

\begin{code}Until then, bear in mind that you can disable termination checking using the `no-termination` flag:
{-@ LIQUID "--no-termination" @-}
\end{code}
