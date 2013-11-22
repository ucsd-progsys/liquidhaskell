---
layout: post
title: "LiquidHaskell Caught Telling Lies!"
date: 2013-11-19 16:12
comments: true
external-url:
categories: termination
author: Niki Vazou
published: true
demo: TellingLies.hs
---

One crucial goal of a type system is to provide the guarantee, 
memorably phrased by Robin Milner as **well-typed programs don't go wrong**. 
The whole point of LiquidHaskell (and related refinement and 
dependent type systems) is to provide the above guarantee for 
expanded notions of "going wrong". All this time, we've claimed 
(and believed) that LiquidHaskell provided such a guarantee.

We were wrong. 

LiquidHaskell tells lies.

<!-- more -->


\begin{code}
module TellingLies where

import Prelude  hiding (repeat)
import Language.Haskell.Liquid.Prelude (liquidAssert)
\end{code}

Lets try to catch LiquidHaskell red-handed. We need: 

1. a notion of going wrong,
2. a program that clearly goes wrong, and the smoking gun,
3. a report from LiquidHaskell that the program is safe.

Going Wrong
-----------

Lets keep things simple with an old fashioned `div`-ision operator.
A division by zero would be, clearly *going wrong*.

To alert LiquidHaskell to this possibility, we encode "not going wrong"
with the precondition that the denominator be  non-zero.

\begin{code}
{-@ divide :: n:Int -> d:{v:Int | v /= 0} -> Int @-}
divide n 0 = liquidError "how dare you!"
divide n d = n `div` d
\end{code}

A Program That Goes Wrong
-------------------------

Now, consider the function `foo`.

\begin{code}
{-@ foo :: n:Int -> {v:Nat | v < n} @-}
foo n | n > 0     = n - 1
      | otherwise = foo n
\end{code}

Now, `foo` should only be called with strictly positive values. 
In which case, the function returns a `Nat` that is strictly 
smaller than the input. 
The function diverges when called with `0` or negative inputs. 

Note that the signature of `foo` is slightly different, but 
nevertheless, legitimate, as *when* the function returns an 
output, the output is indeed a `Nat` that is *strictly less than* 
the input parameter `n`. Hence, LiquidHaskell happily checks 
that `foo` does indeed satisfy its given type.

So far, nothing has gone wrong either in the program, or 
with LiquidHaskell, but consider this innocent little 
function:

\begin{code}
explode = let z = 0
              x = foo z
          in  2013 `divide` z
\end{code}

Thanks to *lazy evaluation*, the call to `foo` is ignored,
and hence evaluating `explode` leads to a crash! Ugh!

What Says LiquidHaskell
-----------------------

However, LiquidHaskell produces a polyannish prognosis and 
cheerfully declares the program **Safe**. 

Looks like LiquidHaskell (and hence, we!) have been caught red-handed.

In our defence, the above, sunny prognosis is not *completely* misguided. 
If Haskell was like ML and had *strict evaluation* then indeed the program 
would be safe in that it might diverge, but at least we would not suffer 
the indignity of a divide-by-zero.  That is, *if* we had strict semantics, 
LiquidHaskell would indeed provide Milner's guarantee.

But of course, thats a pretty lame excuse, since we don't have strict
semantics. So. Is there a way to prevent LiquidHaskell from telling lies?

(Spoiler alert: yes.)
