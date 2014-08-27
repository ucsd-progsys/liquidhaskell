-- | Trivial test for effects

module Eff0 (test0, test1) where

import Data.IORef

{-@ type IntN N = {v:Int | v = N} @-}

{-@ test0 :: IO (IntN {0}) @-}
test0 :: IO Int
test0 = do p  <- newIORef   0
           _  <- writeIORef p 10
           v1 <- readIORef  p
           return v1

{-@ test1 :: IO (IntN {0}, IntN {10}) @-}
test1 :: IO (Int, Int)
test1 = do p  <- newIORef   0
           v0 <- readIORef  p
           _  <- writeIORef p 10
           v1 <- readIORef  p
           return (v0, v1)
