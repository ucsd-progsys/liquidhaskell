-- | Trivial test for effects

module Eff0 (test0, test1) where

import EffSTT

{-@ type IntN N = {v:Int | v = N} @-}

{-@ test0 :: STT (IntN {10}) @-}
test0 :: STT Int
test0 = do p  <- newPtr 0
           _  <- writePtr p 10
           v1 <- readPtr p
           return v1

{-@ test1 :: STT (IntN {0}, IntN {10}) @-}
test1 :: STT (Int, Int)
test1 = do p  <- newPtr   0
           v0 <- readPtr  p
           _  <- writePtr p 10
           v1 <- readPtr  p
           return (v0, v1)
