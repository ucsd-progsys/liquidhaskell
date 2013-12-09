---
layout: post
title: "Getting To the Bottom"
date: 2013-12-02 16:12
comments: true
external-url:
categories: termination
author: Ranjit Jhala, Niki Vazou
published: true 
demo: TellingLies.hs
---

[Previously][ref-lies], we caught LiquidHaskell telling a lie. Today, lets try to
get to the bottom of this mendacity, in order to understand how we can ensure
that it always tells the truth.

<!-- more -->

\begin{code}
module GettingToTheBottom where
\end{code}

The Truth Lies At the Bottom
----------------------------

To figure out how we might prevent falsehoods, lets try to understand 
whats really going on. We need to go back to the beginning.

\begin{code} Recall that the refinement type:
{v:Int | 0 <= v}
\end{code}

is supposed to denote the set of `Int` values that are greater than `0`.

\begin{code} Consider a function:
fib :: {n:Int | 0 <= n} -> {v:Int | 0 <= v}
fib n = e
\end{code}

Intuitively, the type signature states that when checking the body `e` 
we can **assume** that `0 <= n`. 

This is indeed the case with **strict** evaluation, as we are guaranteed 
that `n` will be evaluated before `e`. Thus, either:

1. `n` diverges and so we don't care about `e` as we won't evaluate it, or,
2. `n` is a non-negative value.

Thus, either way, `e` is only evaluated in a context where `0 <= n`.

But this is *not* the case with **lazy** evaluation, as we may 
well start evaluating `e` without evaluating `n`. Indeed, we may
*finish* evaluating `e` without evaluating `n`. 

Of course, *if* `n` is evaluated, it will yield a non-negative value, 
but if it is not (or does not) evaluate to a value, we **cannot assume** 
that the rest of the computation is dead (as with eager evaluation). 

\begin{code} That is, with lazy evaluation, the refinement type `{n:Int | 0 <= n}` *actually* means:
(n = _|_) || (0 <= n)
\end{code}

Keeping LiquidHaskell Honest
----------------------------

One approach to forcing LiquidHaskell to telling the truth is to force 
it to *always* split cases and reason about `_|_`.

\begin{code} Lets revisit `explode`
explode = let z = 0
          in  (\x -> 2013 `divide` z) (foo z)
\end{code}

\begin{code}The case splitting prevents the cheerful but bogus prognosis that `explode` above was safe, because the SMT solver cannot prove that at the call to `divide` 
    z == 0 && (x = _|_ || (x >= 0 && x < z))  => z /= 0
\end{code}

But alas, this cure is worse than the disease. 
It would end up lobotomizing LiquidHaskell making it unable to prove even trivial things like:

\begin{code}_
{-@ trivial    :: x:Int -> y:Int -> {pf: () | x < y} -> Int @-}
trivial x y pf = liquidAssert (x < y) 10
\end{code}

\begin{code}as the corresponding SMT query
    (pf = _|_ || x < y) => (x < y)
\end{code}

is, thanks to the pesky `_|_`, not valid. 

Terminating The Bottom
----------------------

Thus, to make LiquidHaskell tell the truth while also not just pessimistically 
rejecting perfectly good programs, we need a way to get rid of the `_|_`. That 
is, we require a means of teaching LiquidHaskell to determine when a value
is *definitely* not bottom. 

In other words, we need to teach LiquidHaskell how to prove that a computation 
definitely terminates.

[ref-lies]:  /blog/2013/11/23/telling_lies.lhs/ 
