---
layout: post
title: "Termination Checking I"
date: 2013-12-08 16:12
comments: true
external-url:
categories: termination
author: Ranjit Jhala, Niki Vazou
published: false 
demo: Termination1.hs
---

As explained in the [last][ref-lies] [two][ref-bottom] posts, we need a termination
checker to ensure that LiquidHaskell is not tricked by divergent, lazy
computations into telling lies. Well, proving termination is not easy, 
but happily, it turns out that with very little retrofitting, and a 
bit of jiu jitsu, we can use refinements themselves to prove termination!

<!-- more -->

\begin{code}
module Termination where

import Prelude     hiding (sum)
import Data.Vector hiding (sum)
\end{code}

Next, lets see how LiquidHaskell proves termination on simple 
recursive functions, and then later, we'll see how to look at 
fancier cases.

Looping Over Vectors
--------------------

As a running example, lets write a bunch of little functions 
that operate on 1-dimensional vectors

\begin{code}
type Val  = Int
type Vec = Vector Val
\end{code}

Next, lets write a simple recursive function that loops over to add up
the first `n` elements of a vector:

\begin{code}
sum     :: Vec -> Int -> Val
sum a 0 = 0
sum a n = (a ! (n-1)) + sum a (n-1)
\end{code}

Proving Termination By Hand(waving) 
-----------------------------------

OK. Does `sum` terminate? 

First off, it is apparent that if we call `sum` with a
negative `n` then it **will not** terminate. 
Thus, we should only call `sum` with non-negative integers.

Fine, lets assume `n` is non-negative. Why then does it terminate?

Intuitively,

1. If `n` is `0` then it trivially returns with the value `0`.

2. If `n` is non-zero, then we recurse *but* with a strictly smaller `n` ...

3. ... but ultimately hit `0` at which point it terminates.

Thus we can, somewhat more formally, prove termination by induction on `n`. 

**Base Case** `n == 0` The function clearly terminates for the base case input of `0`.

**Inductive Hypothesis** Lets assume that `sum` terminates on all `0 <= k < n`.

**Inductive Step** Prove that `sum n` only recursively invokes `sum` with values that
satisfy the inductive hypothesis and hence, which terminate.

This reasoning suffices to convince ourselves that `sum i` terminates for 
every natural number `i`. That is, we have shown that `sum` terminates 
because a *well-founded metric* (i.e., the natural number `i`) is decreasing 
at each recursive call.

Proving Termination By Types
----------------------------

We can teach LiquidHaskell to prove termination by applying the same reasoning 
as above, by rephrasing it in terms of refinement types.

First, we specify that the input is restricted to the set of `Nat`ural numbers

\begin{code}
{-@ sum :: a:Vec -> {v:Nat | v < (vlen a)} -> Val @-}
\end{code}

where recall that `Nat` is just the refinement type `{v:Int | v >= 0}`.

Second, we typecheck the *body* of `sum` under an environment that
restricts `sum` to only be called on inputs less than `n`, i.e. using
an environment:

-  `a   :: Vec`
-  `n   :: Nat`
-  `sum :: Vec -> n':{v:Nat | v < n} -> Val`

This ensures that any (recursive) call in the body only calls `sum` 
with inputs smaller than the current parameter `n`. Since its body 
typechecks in this environment, i.e. `sum` is called with `n-1` which 
is smaller than `n` and, in this case, a `Nat`, LiquidHaskell proves 
that sum terminates for all `n`.

For those keeping track at home, this is the technique of 
[sized types](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.124.5589), 
which is itself an instance of the classical method of proving termination 
via well founded metrics that goes back at least, to
[Turing](http://www.turingarchive.org/viewer/?id=462&title=01b).

Choosing the Correct Argument
-----------------------------

The example above is quite straightforward, and you might well wonder if this
simple method works well for ``real-world" programs. With a few generalizations
and extensions, and by judiciously using the wealth of information captured in
refinement types, the answer is an emphatic, yes!

Lets see one simple extension today.

We saw that liquidHaskell can happily check that some Natural number is decreasing
at each iteration, but it uses a na&#239;ve heuristic to choose which one -- for
now, assume that it always chooses *the first* `Int` parameter.

As you might imagine, this is quite daft. Consider, a tail-recursive implementation of `sum`:

\begin{code}
{-@ sum' :: a:Vec -> Val -> {v:Nat| v < (vlen a)} -> Val @-}
sum' :: Vec -> Val -> Int -> Val
sum' a acc 0 = acc + a!0 
sum' a acc n = sum' a (acc + a!n) (n-1)
\end{code}

Clearly, the proof fails as liquidHaskell wants to prove that the `acc`umulator 
is a `Nat`ural number that decreases at each iteration, neither of which may be
true.

\begin{code}The remedy is simple. We can direct liquidHaskell to the correct argument `n` using a `Decrease` annotation: 
{-@ Decrease sum' 3 @-}
\end{code}
which directs liquidHaskell to check whether the *third* argument (i.e., `n`) is decreasing. 
With this hint, liquidHaskell will happily verify that `sum'` is indeed a terminating function.

Thats all for now, next time we'll see how the basic technique can be extended
to a variety of sophisticated, real-world settings.


[ref-lies]:  /blog/2013/11/23/telling-lies.lhs/ 
[ref-bottom]: /blog/2013/12/01/getting-to-the-bottom.lhs/
