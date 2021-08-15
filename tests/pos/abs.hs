module AbsPosTest where

{-@ f :: Int -> {n:Int | n >= 0} @-}
f :: Int -> Int
f x = abs x
