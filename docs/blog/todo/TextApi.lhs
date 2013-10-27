---
layout: post
title: "Text Api"
date:
comments: true
external-url:
author: Eric Seidel
published: false
categories: benchmarks
demo: TextApi.hs
---


<!-- more -->

\begin{code}
{-# LANGUAGE MagicHash, BangPatterns #-}
{-@ LIQUID "--no-termination" @-}
module TextApi where

import GHC.Base
import GHC.ST
import Data.Bits ((.&.))
import Data.Word

import qualified TextInternal as I
import TextInternal (Text(..), Array(..), MArray(..))
import TextAux

import Language.Haskell.Liquid.Prelude
\end{code}

Reading
-------

\begin{code}
{-@ measure numchars :: Array -> Int -> Int -> Int @-}
{-@ measure tlength :: Text -> Int
    tlength (Text a o l) = (numchars a o l)
  @-}

{-@ invariant {v:Text | (numchars (tarr v) (toff v) 0)         = 0} @-}
{-@ invariant {v:Text | (numchars (tarr v) (toff v) (tlen v)) >= 0} @-}
{-@ invariant {v:Text | (numchars (tarr v) (toff v) (tlen v)) <= (tlen v)} @-}

{-@ invariant {v:Text | (((tlength v) = 0) <=> ((tlen v) = 0))} @-}
{-@ invariant {v:Text | (tlength v) >= 0} @-}
{-@ invariant {v:Text | (tlen v)    >= 0} @-}
{-@ invariant {v:Text | (tlength v) = (numchars (tarr v) (toff v) (tlen v))} @-}

{-@ predicate SpanChar D A O L I = (((numchars (A) (O) ((I-O)+D)) = (1 + (numchars (A) (O) (I-O))))
                                 && ((numchars (A) (O) ((I-O)+D)) <= (numchars A O L))
                                 && (((I-O)+D) <= L))
  @-}

{-@ unsafeIndexF :: a:Array -> o:AValidO a -> l:AValidL o a
                 -> i:{v:Int | (Btwn (v) (o) (o + l))}
                 -> {v:Word16 | (if (BtwnI v 55296 56319)
                                 then (SpanChar 2 a o l i)
                                 else (SpanChar 1 a o l i))}
  @-}
unsafeIndexF :: Array -> Int -> Int -> Int -> Word16
unsafeIndexF a o l i = let x = I.unsafeIndex a i
                       in liquidAssume (unsafeIndexFQ x a o l i) x

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
          shiftR (I# x#) (I# i#) = I# (x# `iShiftRA#` i#)

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
                  let top' = (top + 1) * 2 --LIQUID `shiftL` 1
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



