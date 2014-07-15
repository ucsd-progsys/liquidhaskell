module Test0 () where

{-@ assert myabs :: x:Int -> {v: Int | v = (if x > 0 then x else (0 - x)) } @-}
myabs :: Int -> Int
myabs x | x > 0     = x
        | otherwise = (0 - x)
