---
layout: post
title: "Text Bug"
date:
comments: true
external-url:
author: Eric Seidel
published: false
categories: benchmarks
demo: TextBug.hs
---


<!-- more -->

\begin{code}
{-# LANGUAGE MagicHash, BangPatterns #-}
{-@ LIQUID "--no-termination" @-}
module TextBug where

import GHC.Base
import GHC.ST
import Data.Bits ((.&.))
import Data.Word

import qualified TextInternal as I
import TextInternal (Text(..), Array(..), MArray(..))
import TextApi
import TextAux

import Language.Haskell.Liquid.Prelude
\end{code}

\begin{code}
{-@ qualif MALenLE(v:int, a:I.MArray s): v <= (malen a) @-}
{-@ qualif ALenLE(v:int, a:I.Array): v <= (alen a) @-}

{-@ qualif Foo(v:a, a:I.MArray s):
        (snd v) <= (malen a)
  @-}
{-@ qualif Foo(v:a, a:I.Array):
        (snd v) <= (alen a)
  @-}

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
