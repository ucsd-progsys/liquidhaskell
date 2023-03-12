{-@ LIQUID "--expect-error-containing=AbsNegTest.hs:6:1" @-}
module AbsNegTest where

{-@ f :: Int -> {n:Int | n < 0} @-}
f :: Int -> Int
f x = abs x
