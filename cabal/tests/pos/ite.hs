module Test0 where

{-@ liquidAssertB myabs :: x:Int -> {v: Int | ((x > 0) ? (v = x) : (v + x = 0)) } @-}
myabs :: Int -> Int
myabs x | x > 0     = x
        | otherwise = (0 - x)
