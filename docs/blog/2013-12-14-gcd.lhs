---
layout: post
title: "Checking Termination"
date: 2013-12-14 16:12
comments: true
external-url:
categories: termination, refinements
author: Niki Vazou
published: false 
demo: GCD.hs
---

In the [last post][ref-termination], we saw how LiquidHaskell can be used to
prove termination. A crucial feature of the termination prover is that it is 
not syntactically driven, i.e. is not limited to say, structural recursion. 
Instead, it uses the wealth of information captured by refinements that are
at our disposal, in order to prove termination. As you might imagine, this
turns out to be crucial in practice.

As a quick toy example -- motivated by a question by [Elias][comment-elias] -- 
lets see how, unlike purely syntax-directed (structural) approaches, 
LiquidHaskell proves that recursive functions, such as Euclid's argument
swapping GCD algorithm, terminates.

<!-- more -->

<div class="row-fluid">
   <div class="span12 pagination-centered">
       <img src="http://faculty.etsu.edu/gardnerr/Geometry-History/Euclid_7-Raphael.jpg"
       alt="Euclid" width="300">
       <br>
         <br>
          <br>
           If Euclid had LiquidHaskell, he wouldn't have to wave his hands.
           <!-- How do you prove his algorithm will <b>terminate?</b> -->
          <br>
         <br>
       <br>
   </div>
</div>

\begin{code}
module GCD where

import Prelude hiding (gcd, mod)

mod :: Int -> Int -> Int
gcd :: Int -> Int -> Int
\end{code}

The [Euclidean algorithm][ref-euclidean] is one of the oldest numerical algorithms 
still in common use and calculates the the greatest common divisor (GCD) of two 
natural numbers `a` and `b`.

Assume that `a > b` and consider the following implementation of `gcd`

\begin{code}
{-@ gcd :: a:Nat -> b:{v:Nat | v < a} -> Int @-}
gcd a 0 = a
gcd a b = gcd b (a `mod` b)
\end{code}

From our previous post, to prove that `gcd` is terminating, it suffices to prove
that the first argument decreases as each recursive call.

By `gcd`'s type signature, `a < b` holds at each iteration, thus liquidHaskell 
will happily discharge the terminating condition.

The only condition left to prove is that `gcd`'s second argument, ie., `a `mod`
b` is less that `b`. 

This property follows from the behavior of the `mod` operator.

So, to prove `gcd` terminating, liquidHaskell needs a refined signature for 
`mod` that captures this behavior, i.e., that for any `a` and `b` the value 
`mod a b` is less than `b`. Fortunately, we can stipulate this via a refined
type:

\begin{code}
{-@ mod :: a:Nat -> b:{v:Nat| (0 < v && v < a)} -> {v:Nat | v < b} @-}
mod a b 
  | a - b >  b = mod (a - b) b
  | a - b <  b = a - b
  | a - b == b = 0
\end{code}

\begin{code}Euclid's original version of `gcd` is different
gcd' :: Int -> Int -> Int
gcd' a b | a == b = a
         | a >  b = gcd' (a - b) b 
         | a <  b = gcd' a (b - a) 
\end{code}

Though this version is simpler, turns out
that LiquidHaskell needs a more sophisticated mechanism to prove it
terminates.
Concretely, to prove `gcd'` terminates, 
liquidHaskell is equipped with a different notion of ordering, namely 
*lexicographic ordering*.

Stay tuned!


[ref-euclidean]:    http://en.wikipedia.org/wiki/Euclidean_algorithm
[ref-termination]:  /blog/2013/12/09/checking-termination.lhs/ 
[ref-lies]:  /blog/2013/11/23/telling-lies.lhs/ 
[ref-bottom]: /blog/2013/12/01/getting-to-the-bottom.lhs/
[comment-elias]: http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/blog/2013/12/09/checking-termination.lhs/#comment-1159606500
