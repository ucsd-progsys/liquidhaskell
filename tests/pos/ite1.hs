module Test0 () where

{-@ assert myabs :: x:Int -> {v: Int | v = ((x > 0) ? x : (0 - x)) } @-}
myabs :: Int -> Int
myabs x | x > 0     = x
        | otherwise = (0 - x)
