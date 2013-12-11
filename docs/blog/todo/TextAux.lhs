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

import qualified TextInternal as I
import TextInternal -- (Text(..))

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

{-@ runText :: (forall s. (m:I.MArray s -> MAValidO m -> ST s Text) -> ST s Text)
            -> Text
  @-}
runText :: (forall s. (I.MArray s -> Int -> ST s Text) -> ST s Text) -> Text
runText act = runST (act $ \ !marr !len -> do
                             arr <- I.unsafeFreeze marr
                             return $! Text arr 0 len)

{-@ qualif MALen(v:Int, a:MArray s): v = malen(a) @-}
{-@ qualif MALen(v:MArray s, i:Int): i = malen(v) @-}

{-@ qualif MALenLE(v:int, a:I.MArray s): v <= (malen a) @-}
{-@ qualif ALenLE(v:int, a:I.Array): v <= (alen a) @-}

{-@ qualif Foo(v:a, a:I.MArray s):
        (snd v) <= (malen a)
  @-}
{-@ qualif Foo(v:a, a:I.Array):
        (snd v) <= (alen a)
  @-}

{-@ qualif Ord(v:int, x:Char)
        : ((((ord x) <  65536) => (v = 0))
        && (((ord x) >= 65536) => (v = 1)))
  @-}
{-@ qualif Ord(v:int, i:int, x:Char)
        : ((((ord x) <  65536) => (v = i))
        && (((ord x) >= 65536) => (v = (i + 1))))
  @-}
{-@ qualif Ord(v:Char, i:int)
        : ((((ord x) <  65536) => (v >= 0))
        && (((ord x) >= 65536) => (v >= 1)))
  @-}

{-@ qualif LTPlus(v:int, a:int, b:int) : v < (a + b) @-}
{-@ qualif LTEPlus(v:int, a:int, b:int) : (v + a) <= b @-}

{-@ qualif Foo(v:int): v >= -1 @-}
{-@ qualif Foo(v:int): v >=  4 @-}

{-@ unsafeIndexFQ :: x:Word16 -> a:Array -> o:Int -> l:Int -> i:Int
                  -> {v:Bool | ((Prop v) <=> (if (BtwnI x 55296 56319)
                                              then (SpanChar 2 a o l i)
                                              else (SpanChar 1 a o l i)))}
  @-}
unsafeIndexFQ :: Word16 -> Array -> Int -> Int -> Int -> Bool
unsafeIndexFQ = undefined

{-@ predicate Btwn V X Y   = ((X <= V) && (V < Y)) @-}
{-@ predicate BtwnE V X Y  = ((X < V)  && (V < Y)) @-}
{-@ predicate BtwnI V X Y  = ((X <= V) && (V <= Y)) @-}
{-@ predicate BtwnEI V X Y = ((X < V)  && (V <= Y)) @-}

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

{-@ measure tarr :: Text -> Array
    tarr (Text a o l) = a
  @-}

{-@ measure toff :: Text -> Int
    toff (Text a o l) = o
  @-}


\end{code}
