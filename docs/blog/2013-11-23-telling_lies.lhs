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
memorably phrased by Milner as *well-typed programs don't go wrong*. 
The whole point of LiquidHaskell (and related refinement and 
dependent type systems) is to provide the above guarantee for 
expanded notions of "going wrong". All this time, we've claimed 
(and believed) that LiquidHaskell provided such a guarantee.

We were wrong. 

LiquidHaskell tells lies.

<!-- more -->


\begin{code}
{-@ LIQUID "--no-termination" @-}

module TellingLies where

divide  :: Int -> Int -> Int
foo     :: Int -> Int
explode :: Int
\end{code}

To catch LiquidHaskell red-handed, we require

1. a notion of **going wrong**,
2. a **program** that clearly goes wrong, and the smoking gun,
3. a **lie** from LiquidHaskell that the program is safe.

The Going Wrong
---------------

Lets keep things simple with an old fashioned `div`-ision operator.
A division by zero would be, clearly *going wrong*.

To alert LiquidHaskell to this possibility, we encode "not going wrong"
with the precondition that the denominator be  non-zero.

\begin{code}
{-@ divide :: n:Int -> d:{v:Int | v /= 0} -> Int @-}
divide n 0 = liquidError "how dare you!"
divide n d = n `div` d
\end{code}

The Program 
-----------

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

The Lie
-------

However, LiquidHaskell produces a polyannish prognosis and 
cheerfully declares the program **Safe**. 

Huh?

Well, LiquidHaskell deduces that

a. `z == 0`  from the binding,
b. `x : Nat` from the output type for `foo`
c. `x <  z`  from the output type for `foo`

Of course, no such `x` exists! That is, LiquidHaskell deduces that
the call to `divide` happens in an *impossible* environment, i.e.
is dead code, and hence, the program is safe.

Thus, in our defence, the above, sunny prognosis is not *completely* 
misguided. If Haskell was like ML and had *strict evaluation* then 
indeed the program would be safe in that we would *not* go wrong 
i.e. would not crash with a divide-by-zero.  

But of course, thats a pretty lame excuse, since we don't have 
strict semantics, and so looks like LiquidHaskell (and hence, we) 
have been caught red-handed.

Well then, is there a way to prevent LiquidHaskell from telling lies?
That is, can we get Milner's *well-typed programs don't go wrong* 
guarantee under lazy evaluation? 

(Spoiler alert: thankfully, yes.)
