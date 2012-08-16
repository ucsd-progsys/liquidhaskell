module Test0 where

{-@ reftype PosInt = {v: Int | v >= 0} @-}

{-@ assert myabs :: Int -> PosInt @-}
myabs :: Int -> Int
myabs x = if (x > 0) then x else (0 - x)

