---
layout: post
title: "Text Read"
date:
comments: true
external-url:
author: Eric Seidel
published: false
categories: benchmarks, text
demo: TextRead.hs
---

Welcome back, today we're going to show how to consume
`Text` values. The key complication we'll find when reasoning about
`Text`s is the use of UTF-16 as the internal encoding.

<!-- more -->

\begin{code}
{-# LANGUAGE BangPatterns #-}
{-@ LIQUID "--no-termination" @-}
module TextApi where

import Data.Word (Word16)

import qualified TextInternal as I
import TextInternal (Text(..), Array(..), MArray(..))
import TextAux

import Language.Haskell.Liquid.Prelude
\end{code}

Let's begin with a simple example, `unsafeHead`.

\begin{code}
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
`off + _len <= alen arr` and we get that `off < alen arr`, which satisfies
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
                 -> i:{v:Nat | (o <= v && v < (o + l))}
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
*must* be a valid index if a lead surrogate is at index `i`.

\begin{code} We can encode these properties in the refinement logic as follows.
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
          n = I.unsafeIndex arr (off+1)
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
\begin{code} `tlength` is a simple wrapper around `numchars`.
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
