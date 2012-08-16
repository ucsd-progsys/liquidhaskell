module Test0 where

{-@ reftype NegInt = {v: Int | v <= 0} @-}

{-@ assert myabs :: Int -> NegInt @-}
myabs :: Int -> Int
myabs x = if (x > 0) then x else (0 - x)

