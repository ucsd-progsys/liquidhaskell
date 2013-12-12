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

Welcome back, today we're going to show how to build and consume
`Text` values. The key complication we'll find when reasoning about
`Text`s is that the use of UTF-16 as the internal encoding.

<!-- more -->

\begin{code}
{-# LANGUAGE BangPatterns #-}
{-@ LIQUID "--no-termination" @-}
module TextWrite where

import GHC.Base (ord)
import GHC.ST
import Data.Bits ((.&.))
import Data.Word

import qualified TextInternal as I
import TextInternal (Text(..), Array(..), MArray(..))
import TextAux

import Language.Haskell.Liquid.Prelude
\end{code}


\begin{code}
{-@ predicate One C = ((ord C) <  65536) @-}
{-@ predicate Two C = ((ord C) >= 65536) @-}

{-@ predicate Room MA I C = (((One C) => (MAValidIN MA I 1))
                          && ((Two C) => (MAValidIN MA I 2))) @-}
{-@ predicate MAValidIN  MA I N = (0 <= I && I <= ((malen MA) - N)) @-}

{-@ writeChar :: ma:MArray s -> i:Nat -> {v:Char | (Room ma i v)}
              -> ST s (MAValidL i ma)
  @-}
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



