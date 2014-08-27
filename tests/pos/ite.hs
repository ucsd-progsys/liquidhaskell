module Test0 () where

{-@ assert myabs :: x:Int -> {v: Int | if x > 0 then v = x else v + x = 0 } @-}
myabs :: Int -> Int
myabs x | x > 0     = x
        | otherwise = (0 - x)
