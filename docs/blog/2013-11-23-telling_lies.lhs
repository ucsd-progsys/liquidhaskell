---
layout: post
title: "LiquidHaskell Caught Telling Lies!"
date: 2013-11-23 16:12
comments: true
external-url:
categories: termination
author: Ranjit Jhala 
published: true
demo: TellingLies.hs
---

One crucial goal of a type system is to provide the guarantee, 
memorably phrased by Milner as *well-typed programs don't go wrong*. 
The whole point of LiquidHaskell (and related systems) is to provide
the above guarantee for expanded notions of "going wrong". 
All this time, we've claimed (and believed) that LiquidHaskell 
provided such a guarantee.

We were wrong. 

LiquidHaskell tells lies.

<!-- more -->

\begin{code}
{-@ LIQUID "--no-termination" @-}

module TellingLies where

import Language.Haskell.Liquid.Prelude (liquidError)

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
divide n 0 = liquidError "no you didn't!"
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
          in  (\x -> (2013 `divide` z)) (foo z)
\end{code}

Thanks to *lazy evaluation*, the call to `foo` is ignored,
and hence evaluating `explode` leads to a crash! Ugh!

The Lie
-------

However, LiquidHaskell produces a polyannish prognosis and 
cheerfully declares the program *safe*. 

Huh?

Well, LiquidHaskell deduces that

a. `z == 0`  from the binding,
b. `x : Nat` from the output type for `foo`
c. `x <  z`  from the output type for `foo`

\begin{code} Of course, no such `x` exists! Or, rather, the SMT solver reasons
    z == 0 && x >= 0 && x < z  => z /= 0
\end{code}

as the hypotheses are inconsistent. In other words, LiquidHaskell 
deduces that the call to `divide` happens in an *impossible* environment,
i.e. is dead code, and hence, the program is safe.

In our defence, the above, sunny prognosis is not *totally misguided*. 
Indeed, if Haskell was like ML and had *strict evaluation* then 
indeed the program would be safe in that we would *not* go wrong 
i.e. would not crash with a divide-by-zero.  

But of course, thats a pretty lame excuse, since Haskell doesn't have 
strict semantics. So looks like LiquidHaskell (and hence, we) 
have been caught red-handed.

Well then, is there a way to prevent LiquidHaskell from telling lies?
That is, can we get Milner's *well-typed programs don't go wrong* 
guarantee under lazy evaluation? 

Thankfully, there is.
