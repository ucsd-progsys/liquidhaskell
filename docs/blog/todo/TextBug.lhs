---
layout: post
title: "Text Bug"
date:
comments: true
external-url:
author: Eric Seidel
published: false
categories: benchmarks, text
demo: TextBug.hs
---

For our last post on `text`, we return to the topic of building a new `Text`
value, i.e. proving the safety of write operations.

<!-- more -->

\begin{code}
{-# LANGUAGE BangPatterns #-}
{-@ LIQUID "--no-termination" @-}
module TextBug where

import GHC.Base (ord)
import GHC.ST (runST)

import qualified TextInternal as I
import TextInternal (Text(..), Array(..), MArray(..))
import TextAux
import TextWrite
\end{code}

Let's take a look at `mapAccumL`, which combines a map and a fold
over a `Stream` and bundles the result of the map into a new `Text`.
Again, we'll want to focus our attention on the `Yield` case of the
inner loop.

\begin{code}
mapAccumL f z0 (Stream next0 s0 len) =
  (nz, Text na 0 nl)
 where
  mlen = upperBound 4 len
  (na,(nz,nl)) = runST $ do
       (marr,x) <- (I.new mlen >>= \arr ->
                    outer arr mlen z0 s0 0)
       arr      <- I.unsafeFreeze marr
       return (arr,x)
  outer arr top = loop
   where
    loop !z !s !i =
      case next0 s of
        Done          -> return (arr, (z,i))
        Skip s'       -> loop z s' i
        Yield x s'
          | j >= top  -> do
            let top' = (top + 1) `shiftL` 1
            arr' <- I.new top'
            I.copyM arr' 0 arr 0 top
            outer arr' top' z s i
          | otherwise -> do
            let (z',c) = f z x
            d <- writeChar arr i c
            loop z' s' (i+d)
          where j | ord x < 0x10000 = i
                  | otherwise       = i + 1
\end{code}

If you recall `unstream` from last time, you'll notice that this loop body
looks almost identical to the one found in `unstream`, but LiquidHaskell has
flagged the `writeChar` call as unsafe! What's going on here?

Let's take a look at `j`, recalling that it carried a crucial part of the safety
\begin{code} proof last time, and see what LiquidHaskell was able to infer.
{v:Int | ((ord x >= 65536) => (v == i+1))
      && ((ord x <  65536) => (v == i))}
\end{code}

Well that's not very useful at all! LiquidHaskell can prove that it's safe to
write `x` but here we are trying to write `c` into the array. This is actually
a *good* thing though, because `c` is the result of calling an arbitrary
function `f` on `x`! We haven't constrained `f` in any way, so it could easily
return a character above `U+10000` given any input.

So `mapAccumL` is actually *unsafe*, and our first wild bug caught by
LiquidHaskell! The fix is luckily easy, we simply have to lift the
`let (z',c) = f z x` binder into the `where` clause, and change `j` to
depend on `ord c` instead.

\begin{code}
mapAccumL' f z0 (Stream next0 s0 len) =
  (nz, Text na 0 nl)
 where
  mlen = upperBound 4 len
  (na,(nz,nl)) = runST $ do
       (marr,x) <- (I.new mlen >>= \arr ->
                    outer arr mlen z0 s0 0)
       arr      <- I.unsafeFreeze marr
       return (arr,x)
  outer arr top = loop
   where
    loop !z !s !i =
      case next0 s of
        Done          -> return (arr, (z,i))
        Skip s'       -> loop z s' i
        Yield x s'
          | j >= top  -> do
            let top' = (top + 1) `shiftL` 1
            arr' <- I.new top'
            I.copyM arr' 0 arr 0 top
            outer arr' top' z s i
          | otherwise -> do
            d <- writeChar arr i c
            loop z' s' (i+d)
          where (z',c) = f z x
                j | ord c < 0x10000 = i
                  | otherwise       = i + 1
\end{code}

LiquidHaskell happily accepts our revised `mapAccumL`, as did the `text`
maintainers.

We hope you've enjoyed this whirlwind tour of using LiquidHaskell to verify
production code, we have many more examples in the `benchmarks` folder of
our GitHub repository for the intrepid reader.
