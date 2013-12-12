---
layout: post
title: "Checking Termination"
date: 2013-12-14 16:12
comments: true
external-url:
categories: termination, refinements
author: Niki Vazou
published: true 
demo: GCD.hs
---

As explained in the [last][ref-termination] post, liquidHaskell can be used to
prove termination.
A crucial feature of the termination prover is 
that it is not syntactically driven, contrary, it uses 
the wealth of information captured by refinements.
So, contrary to syntax sensitive methods,
it accepts terminating recursive
functions, such as Euclidean Algorithm that swaps its arguments.


<!-- more -->

<div class="row-fluid">
   <div class="span12 pagination-centered">
       <img src="http://faculty.etsu.edu/gardnerr/Geometry-History/Euclid_7-Raphael.jpg"
       alt="Euclid" width="300">
       <br>
       <br>
       <br>
       How do you prove his algorithm will <b>terminate?</b>
       <br>
       <br>
       <br>
   </div>
</div>



\begin{code}
module CGD where

import Prelude hiding (gcd, mod)
\end{code}

[Euclidean algorithm][ref-euclidean] is one of the oldest numerical algorithms still in common
use and calculates the the greatest common divisor (gcd) of two natural numbers
`a` and `b`.

Assume that `a > b` and consider the following implementation of `gcd`

\begin{code}
{-@ gcd :: a:Nat -> b:{v:Nat | v < a} -> Int @-}
gcd     :: Int -> Int -> Int
gcd a 0 = a
gcd a b = gcd b (a `mod` b)
\end{code}

From our previous post, to prove that `gcd` is terminating, it suffices to prove
that the first argument decreases as each recursive call.

By `gcd`'s type signature, `a < b` holds at each iteration, 
thus liquidHaskell will hapily discharge the terminating condition.

The only condition left to prove is that `gcd`'s second argument, ie., `a `mod`
b` is less that `b`. 

But this is a common property of `mod` operator.

So, to prove `gcd` terminating, liquidHaskell needs a refined signature
for `mod` that caputers this behavior, ie., that `mod a b < b`

\begin{code}
{-@ mod :: a:Nat -> b:{v:Nat| ((v < a) && (v > 0))} -> {v:Nat | v < b} @-}
mod :: Int -> Int -> Int
mod a b | a - b >  b = mod (a - b) b
        | a - b <  b = a - b
        | a - b == b = 0
\end{code}


Another implementation of `gcd` decreases *either* `a` *or* `b`.
LiquidHaskell, to prove that 
such an implementation is terminating, is equipped with a different notion of
ordering, namely *lexicographic ordering*.
Stay tuned!

[ref-euclidean]:    http://en.wikipedia.org/wiki/Euclidean_algorithm
[ref-termination]:  /blog/2013/12/09/checking-termination.lhs/ 
[ref-lies]:  /blog/2013/11/23/telling-lies.lhs/ 
[ref-bottom]: /blog/2013/12/01/getting-to-the-bottom.lhs/
