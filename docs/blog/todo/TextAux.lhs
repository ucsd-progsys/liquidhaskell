---
layout: post
title: "Text Aux"
date:
comments: true
external-url:
author: Eric Seidel
published: false
categories: benchmarks
demo: TextAux.hs
---

\begin{code}
{-# LANGUAGE BangPatterns, ExistentialQuantification, Rank2Types, MagicHash #-}
module TextAux where

import GHC.Base hiding (unsafeChr)
import GHC.ST
import Data.Word
import GHC.Word (Word16(..))

import TextInternal

{-@ measure isUnknown :: Size -> Prop
    isUnknown (Exact n) = false
    isUnknown (Max   n) = false
    isUnknown (Unknown) = true
  @-}
{-@ measure getSize :: Size -> Int
    getSize (Exact n) = n
    getSize (Max   n) = n
  @-}
{-@ qualif IsUnknown(v:Size) : (isUnknown v) @-}
{-@ qualif IsKnown(v:Size) : not (isUnknown v) @-}

{-@ invariant {v:Size | (getSize v) >= 0} @-}

data Size = Exact {-# UNPACK #-} !Int -- ^ Exact size.
          | Max   {-# UNPACK #-} !Int -- ^ Upper bound on size.
          | Unknown                   -- ^ Unknown size.
            deriving (Eq, Show)

{-@ upperBound :: k:Nat -> s:Size -> {v:Nat | v = ((isUnknown s) ? k : (getSize s))} @-}
upperBound :: Int -> Size -> Int
upperBound _ (Exact n) = n
upperBound _ (Max   n) = n
upperBound k _         = k

data Step s a = Done
              | Skip !s
              | Yield !a !s

data Stream a =
    forall s. Stream
    (s -> Step s a)             -- stepper function
    !s                          -- current state
    !Size                       -- size hint

{-@ runText :: (forall s. (m:MArray s -> MAValidO m -> ST s Text) -> ST s Text)
            -> Text
  @-}
runText :: (forall s. (MArray s -> Int -> ST s Text) -> ST s Text) -> Text
runText act = runST (act $ \ !marr !len -> do
                             arr <- unsafeFreeze marr
                             return $! Text arr 0 len)

{-@ qualif MALen(v:int, a:MArray s): v = malen(a) @-}
{-@ qualif MALen(v:MArray s, i:int): i = malen(v) @-}

{- invariant {v:MArray s | (malen v) >= 0} @-}
{- invariant {v:Array | (alen v) >= 0} @-}

{-@ qualif MALenLE(v:int, a:MArray s): v <= (malen a) @-}
{-@ qualif ALenLE(v:int, a:Array): v <= (alen a) @-}

{-@ qualif FreezeMArr(v:Array, ma:MArray s): (alen v) = (malen ma) @-}

{-@ qualif Foo(v:a, a:MArray s):
        (snd v) <= (malen a)
  @-}
{-@ qualif Foo(v:a, a:Array):
        (snd v) <= (alen a)
  @-}

{-@ measure ord :: Char -> Int @-}
{-@ GHC.Base.ord :: c:Char -> {v:Int | v = (ord c)} @-}

{-@ qualif Ord(v:int, i:int, x:Char)
        : ((((ord x) <  65536) => (v = i))
        && (((ord x) >= 65536) => (v = (i + 1))))
  @-}

{-@ qualif LTEPlus(v:int, a:int, b:int) : (v + a) <= b @-}

{-@ measure numchars :: Array -> Int -> Int -> Int @-}
{-@ measure tlength :: Text -> Int
    tlength (Text a o l) = (numchars a o l)
  @-}

{-@ predicate SpanChar N A O L I =
      (((numchars (A) (O) ((I-O)+N)) = (1 + (numchars (A) (O) (I-O))))
    && ((numchars (A) (O) ((I-O)+N)) <= (numchars A O L))
    && (((I-O)+N) <= L))
  @-}

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
  where arrEmpty = runST $ new 0 >>= unsafeFreeze

{-@ shiftL :: i:Nat -> n:Nat -> {v:Nat | ((n = 1) => (v = (i * 2)))} @-}
shiftL (I# x#) (I# i#) = I# (x# `iShiftL#` i#)

shiftR (I# x#) (I# i#) = I# (x# `iShiftRA#` i#)

unsafeChr :: Word16 -> Char
unsafeChr (W16# w#) = C# (chr# (word2Int# w#))

chr2 :: Word16 -> Word16 -> Char
chr2 (W16# a#) (W16# b#) = C# (chr# (upper# +# lower# +# 0x10000#))
    where
      !x# = word2Int# a#
      !y# = word2Int# b#
      !upper# = uncheckedIShiftL# (x# -# 0xD800#) 10#
      !lower# = y# -# 0xDC00#

{-@ type MAValidL O A = {v:Nat | (v+O) <= (malen A)} @-}

{-@ type AValidO  A   = {v:Nat | v     <= (alen A)} @-}
{-@ type AValidL O A = {v:Nat | (v+O) <= (alen A)} @-}

{-@ type TValidI T = {v:Nat | v < (tlen T)} @-}

{-@ invariant {v:Text | (tlength v) = (numchars (tarr v) (toff v) (tlen v))} @-}



{-@ qualif Min(v:int, t:Text, i:int):
      (if ((tlength t) < i)
       then ((numchars (tarr t) (toff t) v) = (tlength t))
       else ((numchars (tarr t) (toff t) v) = i))
  @-}

{-@ qualif NumChars(v:int, t:Text, i:int): v = (numchars (tarr t) (toff t) i) @-}

{-@ qualif TLengthLE(v:int, t:Text): v <= (tlength t) @-}

\end{code}
