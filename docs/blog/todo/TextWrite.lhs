---
layout: post
title: "Text Write"
date:
comments: true
external-url:
author: Eric Seidel
published: false
categories: benchmarks, text
demo: TextWrite.hs
---

Last time, we showed how to reason about Unicode and a variable-width
encoding of `Char`s when consuming a `Text` value, today we'll look at
the same issue from the perspective of *building* a `Text`.

<!-- more -->

\begin{code}
{-# LANGUAGE BangPatterns #-}
{-@ LIQUID "--no-termination" @-}
module TextWrite where

import GHC.Base (ord)
import GHC.ST (ST, runST)
import Data.Bits ((.&.))

import qualified TextInternal as I
import TextInternal (Text(..), Array(..), MArray(..))
import TextAux
\end{code}

We mentioned previously that `text` uses stream fusion to optimize
multiple loops over a `Text` into a single loop; as a result many of
the top-level API functions are simple wrappers around equivalent
functions over `Stream`s. The creation of `Text` values is then
largely handled by a single function, `unstream`, which converts a
`Stream` into a `Text`.

\begin{code}
unstream :: Stream Char -> Text
unstream (Stream next0 s0 len) = runText $ \done -> do
  let mlen = upperBound 4 len
  arr0 <- I.new mlen
  let outer arr top = loop
       where
        loop !s !i =
            case next0 s of
              Done          -> done arr i
              Skip s'       -> loop s' i
              Yield x s'
                | j >= top  -> do
                  let top' = (top + 1) `shiftL` 1
                  arr' <- I.new top'
                  I.copyM arr' 0 arr 0 top
                  outer arr' top' s i
                | otherwise -> do
                  d <- writeChar arr i x
                  loop s' (i+d)
                where j | ord x < 0x10000 = i
                        | otherwise       = i + 1
  outer arr0 mlen s0 0
\end{code}

Since we're focusing on memory safety here we won't go into detail
about how `Stream`s work. Let's instead jump right into the inner
`loop` and look at the `Yield` case. Here we need to write a char `x`
into `arr`, so we compute the maximal index `j` to which we will
write -- i.e. if `x >= U+10000` then `j = i + 1` -- and determine
whether we can safely write at `j`. If the write is unsafe we have to
allocate a larger array before continuing, otherwise we write `x` and
increment `i` by `x`s width.

Since `writeChar` has to handle writing *any* Unicode value, we need
to assure it that there will always be room to write `x` into `arr`,
regardless of `x`s width. Indeed, this is expressed in the type we
give to `writeChar`.

\begin{code}
{-@ writeChar :: ma:MArray s -> i:Nat -> {v:Char | (Room v ma i)}
              -> ST s {v:Nat | (RoomN v ma i)}
  @-}
\end{code}

The predicate aliases `Room` and `RoomN` express that a character can
fit in the array at index `i` and that there are at least `n` slots
available starting at `i` respectively.

\begin{code}
{-@ predicate Room C MA I = (((One C) => (RoomN 1 MA I))
                          && ((Two C) => (RoomN 2 MA I)))
  @-}
{-@ predicate RoomN N MA I = (I+N <= (malen MA)) @-}
\end{code}

The `One` and `Two` predicates express that a character will be
encoded in one or two 16-bit words, by reasoning about its ordinal
value.

\begin{code}
{-@ predicate One C = ((ord C) <  65536) @-}
{-@ predicate Two C = ((ord C) >= 65536) @-}
\end{code}

\begin{code} As with `numchars`, we leave `ord` abstract, but inform LiquidHaskell that the `ord` *function* does in fact return the ordinal value of the character.
{-@ measure ord :: Char -> Int @-}
{-@ ord :: c:Char -> {v:Int | v = (ord c)} @-}
\end{code}

Since `writeChar` assumes that it will never be called unless there is room to
write `c`, it is safe to just split `c` into 16-bit words and write them into
the array.

\begin{code}
writeChar :: MArray s -> Int -> Char -> ST s Int
writeChar marr i c
    | n < 0x10000 = do
        I.unsafeWrite marr i (fromIntegral n)
        return 1
    | otherwise = do
        I.unsafeWrite marr i lo
        I.unsafeWrite marr (i+1) hi
        return 2
    where n = ord c
          m = n - 0x10000
          lo = fromIntegral $ (m `shiftR` 10) + 0xD800
          hi = fromIntegral $ (m .&. 0x3FF) + 0xDC00
\end{code}

In typical design-by-contract style, we're putting the burden of proof to
establish safety on `writeChar`s caller. Now, scroll back up to
`unstream` and mouse over `j` to see its inferred type.
\begin{code} You should see something like
{v:Int | ((ord x >= 65536) => (v == i+1))
      && ((ord x <  65536) => (v == i))}
\end{code}
which, combined with the case-split on `j >= top`, provides the proof that
writing `x` will be safe!

Stay tuned, next time we'll look at another example of building a `Text` where
LiquidHaskell fails to infer this crucial refinement...
