{-@ LIQUID "--expect-error-containing=Exponential2NegTest.hs:6:20" @-}
module Exponential2NegTest where

{-@ ex6 :: {n:Float | n /= 0} -> Int -> Float @-}
ex6 :: Float -> Int -> Float
ex6 x y = 1 / (x ^ y)
