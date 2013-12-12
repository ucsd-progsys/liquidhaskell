---
layout: post
title: "Text Api"
date:
comments: true
external-url:
author: Eric Seidel
published: false
categories: benchmarks, text
demo: TextApi.hs
---

Welcome back, today we're going to show how to build and consume
`Text` values. The key complication we'll find when reasoning about
`Text`s is that the use of UTF-16 as the internal encoding.

<!-- more -->

\begin{code}
{-# LANGUAGE BangPatterns #-}
{-@ LIQUID "--no-termination" @-}
module TextApi where

import GHC.Base (ord)
import GHC.ST
import Data.Bits ((.&.))
import Data.Word

import qualified TextInternal as I
import TextInternal (Text(..), Array(..), MArray(..))
import TextAux

import Language.Haskell.Liquid.Prelude
\end{code}

Let's begin with a simple example, `unsafeHead`.

\begin{code}
{-@ measure tlen :: Text -> Int
    tlen (Text a o l) = l
  @-}
{-@ type TextNE = {v:Text | (tlen v) > 0} @-}
{-@ unsafeHead :: TextNE -> Char @-}
unsafeHead :: Text -> Char
unsafeHead (Text arr off _len)
    | m < 0xD800 || m > 0xDBFF = unsafeChr m
    | otherwise                = chr2 m n
    where m = I.unsafeIndex arr off
          n = I.unsafeIndex arr (off+1)
\end{code}

LiquidHaskell can prove the first `I.unsafeIndex` is safe because the
precondition states that the `Text` must not be empty, i.e. `_len > 0`
must hold. Combine this with the core `Text` invariant that
`_len + off <= alen arr` and we get that `off < alen arr`, which satisfies
the precondition for `I.unsafeIndex`.

However, the same calculation *fails* for the second index because we
can't prove that `off + 1 < alen arr`. The solution is going to
require some understanding of UTF-16, so let's take a brief detour.

The UTF-16 standard represents all code points below `U+10000` with a
single 16-bit word; all others are split into two 16-bit words, known
as a *surrogate pair*. The first word, or *lead*, is guaranteed to be
in the range `[0xD800, 0xDBFF]` and the second, or *trail*, is
guaranteed to be in the range `[0xDC00, 0xDFFF]`.

Armed with this knowledge of UTF-16 we can return to
`unsafeHead`. Note the case-split on `m`, which determines whether `m`
is a lead surrogate. If `m` is a lead surrogate then we know there
must be a trail surrogate at `off+1`; we can define a specialized
version of `unsafeIndex` that encodes this domain knowledge.

\begin{code}
{-@ unsafeIndexF :: a:Array -> o:AValidO a -> l:AValidL o a
                 -> i:{v:Int | (o <= v && v < (o + l))}
                 -> {v:Word16 | (if (55296 <= v && v <= 56319)
                                 then (SpanChar 2 a o l i)
                                 else (SpanChar 1 a o l i))}
  @-}
unsafeIndexF :: Array -> Int -> Int -> Int -> Word16
unsafeIndexF a o l i = let x = I.unsafeIndex a i
                       in liquidAssume (axiom_lead_surr x a o l i) x
\end{code}

Our variant `unsafeIndexF` (F as in "forward") takes an array, an
offset, and a length (which together must form a valid `Text`); a
valid index into the `Text`; and returns a `Word16` with an
interesting type. The best way to read this type would be "if `v` is
in the range `[0xD800, 0xDBFF]`, then the character that starts at
index `i` in the array `a` spans two slots, otherwise it only spans
one slot." Intuitively, we know what it means for a character to span
`n` slots, but LiquidHaskell needs to know three things:

1. `a[o:i+n]` contains one more character than `a[o:i]` (borrowing
   Python's wonderful slicing syntax)
2. `a[o:i+n]` contains no more characters than `a[o:l]`
3. `i-o+n <= l`

2 and 3 encode the well-formedness of a `Text` value, i.e. `i+1`
*must* be a valid index if a lead surrogate is at index `i`. We can
encode these properties in the refinement logic as follows.

\begin{code}
{-@ measure numchars :: Array -> Int -> Int -> Int @-}

{-@ predicate SpanChar N A O L I =
      (((numchars (A) (O) ((I-O)+N)) = (1 + (numchars (A) (O) (I-O))))
    && ((numchars (A) (O) ((I-O)+N)) <= (numchars A O L))
    && (((I-O)+N) <= L))
  @-}
\end{code}

The `numchars` measure takes an array, an offset, and a length
(e.g. the `arr`, `off`, and `len` fields of a `Text`) and denotes the
number of characters contained in the `length` slots beginning at
`offset`. Since we can't compute this in the refinement logic, we
leave the measure abstract.

Finally returning to `unsafeHead`, we can use `unsafeIndexF` to
strengthen the inferred type for `m`. LiquidHaskell can now prove that
the second `unsafeIndex` is in fact safe, because it it only demanded
if `m` is a lead surrogate.

\begin{code}
{-@ unsafeHead' :: TextNE -> Char @-}
unsafeHead' :: Text -> Char
unsafeHead' (Text arr off _len)
    | m < 0xD800 || m > 0xDBFF = unsafeChr m
    | otherwise                = chr2 m n
    where m = unsafeIndexF arr off _len off
          {-@ LAZYVAR n @-}
          n = I.unsafeIndex arr (off+1)
\end{code}

\begin{code}
{-@ invariant {v:Text | (numchars (tarr v) (toff v) 0)         = 0} @-}
{-@ invariant {v:Text | (numchars (tarr v) (toff v) (tlen v)) >= 0} @-}
{-@ invariant {v:Text | (numchars (tarr v) (toff v) (tlen v)) <= (tlen v)} @-}


{-@ predicate SpanCharT V T I =
         ((numchars(tarr t) (toff t) (i+v))
          = (1 + (numchars (tarr t) (toff t) i))
      && ((numchars (tarr t) (toff t) (i+v))
          <= (tlength t)))
  @-}

{-@ iter_ :: t:Text -> i:{v:Nat | v < (tlen t)}
          -> {v:Nat | ((BtwnEI (v+i) i (tlen t))
                    && (SpanCharT v t i))}
  @-}
iter_ :: Text -> Int -> Int
iter_ (Text arr off len) i
    | m < 0xD800 || m > 0xDBFF = 1
    | otherwise                = 2
 where m = unsafeIndexF arr off len (off+i)

{-@ qualif Min(v:int, t:Text, i:int):
      (if ((tlength t) < i)
       then ((numchars (tarr t) (toff t) v) = (tlength t))
       else ((numchars (tarr t) (toff t) v) = i))
  @-}

{-@ qualif NumChars(v:int, t:Text, i:int): v = (numchars (tarr t) (toff t) i) @-}

{-@ qualif TLengthLE(v:int, t:Text): v <= (tlength t) @-}

{-@ take :: n:Nat -> t:Text -> {v:Text | (Min (tlength v) (tlength t) n)} @-}
take :: Int -> Text -> Text
take n t@(Text arr off len)
    | n <= 0    = empty
    | n >= len  = t
    | otherwise = Text arr off (loop 0 0)
  where
     loop !i !cnt
          | i >= len || cnt >= n = i
          | otherwise            = let d = iter_ t i
                                   in loop (i+d) (cnt+1)
\end{code}


Writing
-------

\begin{code}
{-@ measure ord :: Char -> Int @-}
{-@ GHC.Base.ord :: c:Char -> {v:Int | v = (ord c)} @-}

{-@ predicate One C = ((ord C) <  65536) @-}
{-@ predicate Two C = ((ord C) >= 65536) @-}

{-@ qualif OneC(v:Char) : ((ord v) <  65536) @-}
{-@ qualif TwoC(v:Char) : ((ord v) >= 65536) @-}

{-@ predicate Room MA I C = (((One C) => (MAValidIN MA I 1))
                          && ((Two C) => (MAValidIN MA I 2))) @-}
{-@ predicate MAValidIN  MA I N = (BtwnI I 0 ((malen MA) - N)) @-}

{-@ writeChar :: ma:I.MArray s -> i:Nat -> {v:Char | (Room ma i v)}
              -> ST s {v:(MAValidL i ma) | (BtwnI v 1 2)}
  @-}
writeChar :: I.MArray s -> Int -> Char -> ST s Int
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



