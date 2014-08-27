---
layout: post
title: "Text Read"
date: 2014-02-16
comments: true
external-url:
author: Eric Seidel
published: false
categories: benchmarks, text
demo: TextRead.hs
---

Welcome back! Last time we left off on a bit of a cliffhanger with the
`unstream` example. Remember, the issue we found was that some `Char`s
can't fit into a single `Word16`, so the safety of a write depends not
only on the *index*, but also on the *value* being written! Before we
can resolve this issue with `unstream` we'll have to learn about
UTF-16, so let's take a short detour and look at how one *consumes* a
`Text`.

<!-- more -->

<div class="hidden">

\begin{code}
{-# LANGUAGE BangPatterns, CPP, MagicHash, Rank2Types,
    RecordWildCards, UnboxedTuples, ExistentialQuantification #-}
{-@ LIQUID "--no-termination" @-}
module TextRead where

import GHC.Base hiding (unsafeChr)
import GHC.ST
import GHC.Word (Word16(..))
import Data.Bits hiding (shiftL)
import Data.Word

import Language.Haskell.Liquid.Prelude


--------------------------------------------------------------------------------
--- From TextInternal
--------------------------------------------------------------------------------

{-@ shiftL :: i:Nat -> n:Nat -> {v:Nat | ((n = 1) => (v = (i * 2)))} @-}
shiftL :: Int -> Int -> Int
shiftL = undefined -- (I# x#) (I# i#) = I# (x# `iShiftL#` i#)

{-@ data Array = Array { aBA  :: ByteArray#
                       , aLen :: Nat 
                       } 
  @-}

data Array = Array {
    aBA  :: ByteArray#
  , aLen :: !Int
  }

{-@ measure alen     :: Array -> Int
    alen (Array a n) = n
  @-}

{-@ aLen :: a:Array -> {v:Nat | v = (alen a)}  @-}

{-@ type ArrayN  N   = {v:Array | (alen v) = N} @-}

{-@ type AValidI A   = {v:Nat | v     <  (alen A)} @-}
{-@ type AValidO A   = {v:Nat | v     <= (alen A)} @-}
{-@ type AValidL O A = {v:Nat | (v+O) <= (alen A)} @-}

{-@ data MArray s = MArray { maBA  :: MutableByteArray# s
                           , maLen :: Nat } @-}

data MArray s = MArray {
    maBA  :: MutableByteArray# s
  , maLen :: !Int
  }

{-@ measure malen :: MArray s -> Int
    malen (MArray a n) = n
  @-}

{-@ maLen :: a:MArray s -> {v:Nat | v = (malen a)}  @-}

{-@ type MArrayN s N = {v:MArray s | (malen v) = N} @-}

{-@ type MAValidO MA = {v:Nat | v <= (malen MA)} @-}

{-@ new :: forall s. n:Nat -> ST s (MArrayN s n) @-}
new          :: forall s. Int -> ST s (MArray s)
new n
  | n < 0 || n .&. highBit /= 0 = error $ "Data.Text.Array.new: size overflow"
  | otherwise = ST $ \s1# ->
       case newByteArray# len# s1# of
         (# s2#, marr# #) -> (# s2#, MArray marr# n #)
  where !(I# len#) = bytesInArray n
        highBit    = maxBound `xor` (maxBound `shiftR` 1)
        bytesInArray n = n `shiftL` 1

{-@ unsafeFreeze :: ma:MArray s -> ST s (ArrayN (malen ma)) @-}
unsafeFreeze :: MArray s -> ST s Array
unsafeFreeze MArray{..} = ST $ \s# ->
                          (# s#, Array (unsafeCoerce# maBA) maLen #)

{-@ unsafeIndex :: a:Array -> AValidI a -> Word16 @-}
unsafeIndex  :: Array -> Int -> Word16
unsafeIndex Array{..} i@(I# i#)
  | i < 0 || i >= aLen = liquidError "out of bounds"
  | otherwise = case indexWord16Array# aBA i# of
                  r# -> (W16# r#)

data Text = Text Array Int Int
{-@ data Text [tlen] = Text (tarr :: Array)
                            (toff :: TValidO tarr)
                            (tlen :: TValidL toff tarr)
  @-}

{-@ type TValidI T   = {v:Nat | v     <  (tlen T)} @-}
{-@ type TValidO A   = {v:Nat | v     <= (alen A)} @-}
{-@ type TValidL O A = {v:Nat | (v+O) <= (alen A)} @-}


--------------------------------------------------------------------------------
--- Helpers
--------------------------------------------------------------------------------

{-@ invariant {v:Text | (tlength v) = (numchars (tarr v) (toff v) (tlen v))} @-}

{-@ axiom_lead_surr :: x:Word16 -> a:Array -> o:Nat -> l:Nat -> i:Nat
                  -> {v:Bool | ((Prop v) <=> (if (55296 <= x && x <= 56319)
                                              then (SpanChar 2 a o l i)
                                              else (SpanChar 1 a o l i)))}
  @-}
axiom_lead_surr :: Word16 -> Array -> Int -> Int -> Int -> Bool
axiom_lead_surr = undefined

{-@ empty :: {v:Text | (tlen v) = 0} @-}
empty :: Text
empty = Text arrEmpty 0 0
  where
    {-@ arrEmpty :: (ArrayN {0}) @-}
    arrEmpty = runST $ new 0 >>= unsafeFreeze

unsafeChr :: Word16 -> Char
unsafeChr (W16# w#) = C# (chr# (word2Int# w#))

chr2 :: Word16 -> Word16 -> Char
chr2 (W16# a#) (W16# b#) = C# (chr# (upper# +# lower# +# 0x10000#))
    where
      !x# = word2Int# a#
      !y# = word2Int# b#
      !upper# = uncheckedIShiftL# (x# -# 0xD800#) 10#
      !lower# = y# -# 0xDC00#

{-@ qualif Min(v:int, t:Text, i:int):
      (if ((tlength t) < i)
       then ((numchars (tarr t) (toff t) v) = (tlength t))
       else ((numchars (tarr t) (toff t) v) = i))
  @-}

{-@ qualif NumChars(v:int, t:Text, i:int): v = (numchars (tarr t) (toff t) i) @-}

{-@ qualif TLengthLE(v:int, t:Text): v <= (tlength t) @-}

\end{code}

</div>

Let's begin with a simple example, `unsafeHead`.

\begin{code}
{-@ type TextNE = {v:Text | (tlen v) > 0} @-}

{-@ unsafeHead :: TextNE -> Char @-}
unsafeHead :: Text -> Char
unsafeHead (Text arr off _len)
    | m < 0xD800 || m > 0xDBFF = unsafeChr m
    | otherwise                = chr2 m n
    where m = unsafeIndex arr off
          n = unsafeIndex arr (off+1)
\end{code}

LiquidHaskell can prove the first `unsafeIndex` is safe because the
precondition states that the `Text` must not be empty, i.e. `_len > 0`
must hold. Combine this with the core `Text` invariant that
`off + _len <= alen arr` and we get that `off < alen arr`, which satisfies
the precondition for `unsafeIndex`.

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
                 -> i:{v:Nat | (o <= v && v < (o + l))}
                 -> {v:Word16 | (if (55296 <= v && v <= 56319)
                                 then (SpanChar 2 a o l i)
                                 else (SpanChar 1 a o l i))}
  @-}
unsafeIndexF :: Array -> Int -> Int -> Int -> Word16
unsafeIndexF a o l i = let x = unsafeIndex a i
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
*must* be a valid index if a lead surrogate is at index `i`.

We can encode these properties in the refinement logic as follows.

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
leave the measure abstract. We can, however, provide LiquidHaskell
with a few invariants about the behavior of `numchars`, specifically
that (1) `numchars` always returns a `Nat`, (2) there are no
characters contained in a empty span, and (3) there are at most as
many characters as words in a `Text`. We encode these using a special
`invariant` annotation.

\begin{code}
{-@ invariant {v:Text | (numchars (tarr v) (toff v) (tlen v)) >= 0}        @-}
{-@ invariant {v:Text | (numchars (tarr v) (toff v) 0)         = 0}        @-}
{-@ invariant {v:Text | (numchars (tarr v) (toff v) (tlen v)) <= (tlen v)} @-}
\end{code}

Finally returning to `unsafeHead`, we can use `unsafeIndexF` to
strengthen the inferred type for `m`. LiquidHaskell can now prove that
the second `unsafeIndex` is in fact safe, because it is only demanded
if `m` is a lead surrogate.

\begin{code}
{-@ unsafeHead' :: TextNE -> Char @-}
unsafeHead' :: Text -> Char
unsafeHead' (Text arr off _len)
    | m < 0xD800 || m > 0xDBFF = unsafeChr m
    | otherwise                = chr2 m n
    where m = unsafeIndexF arr off _len off
          {-@ LAZYVAR n @-}
          n = unsafeIndex arr (off+1)
\end{code}

The `LAZYVAR` annotation is currently required because LiquidHaskell
doesn't know that `n` will only be demanded in one branch; one can
imagine a transformation that would push the `where` bindings inward
to the use-site, which would alleviate this issue.

Before signing off, let's take a look at a slightly more interesting
function, `take`.

\begin{code}
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

`take` gets a `Nat` and a `Text`, and returns a `Text` that contains
the first `n` characters of `t`. That is, unless `n >= tlength t`, in
which case it just returns `t`.

`tlength` is a simple wrapper around `numchars`.

\begin{code}
{-@ measure tlength :: Text -> Int
    tlength (Text a o l) = (numchars a o l)
  @-}
\end{code}

The bulk of the work is done by the
inner `loop`, which has to track the current index `i` and the number
of characters we have seen, `cnt`. `loop` uses an auxiliary function
`iter_` to determine the *width* of the character that starts at `i`,
bumps `cnt`, and recursively calls itself at `i+d` until it either
reaches the end of `t` or sees `n` characters, returning the final
index.

The `iter_` function is quite simple, it just determines whether the
word at index `i` is a lead surrogate, and returns the appropriate
span.

\begin{code}
{-@ predicate SpanCharT N T I =
      (SpanChar N (tarr T) (toff T) (tlen T) ((toff T)+I))
  @-}

{-@ iter_ :: t:Text -> i:TValidI t
          -> {v:Nat | (SpanCharT v t i)}
  @-}
iter_ :: Text -> Int -> Int
iter_ (Text arr off len) i
    | m < 0xD800 || m > 0xDBFF = 1
    | otherwise                = 2
 where m = unsafeIndexF arr off len (off+i)
\end{code}

Again, we use `unsafeIndexF` to learn more about the structure of `t`
by observing a small piece of it. It's also worth noting that we've
encoded all of the domain knowledge we need into a single function,
which has the benefit of letting us focus our attention on one type
when we try to ensure that we've encoded it correctly.

Next time, we'll continue our exploration of `text` and see how to
construct a `Text` while ensuring the absence of out-of-bounds writes.
