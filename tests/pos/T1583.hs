{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--ple" @-}

module T1583 where

{-@ incr :: n:Int -> (m::{v:Int | v > n}, {u:Int | u > m}) @-}
incr :: Int -> (Int, Int)
incr x = (x+1, x+2)

{-@ incr' :: n:Int -> ({v:Int | v > n}, Int) <{\x y -> y > x}> @-}
incr' :: Int -> (Int, Int)
incr' x = (x+1, x+2)

{-@ greater :: n:Int -> m:{Int | m > n} @-}
greater :: Int -> Int
greater x = y where (y,_) = incr x -- changing incr' to incr breaks the proof

{-@ unsafe :: (xs::{v:Int| v <= 0 }, ()) -> {v:Int| v <= 0 } @-}
unsafe :: (Int, ()) -> Int
unsafe (xs, _) = xs 