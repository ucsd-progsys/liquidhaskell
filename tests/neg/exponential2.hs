-- negative test for real exponentiation
module Foo where

{-@ ex6 :: {n:Float | n /= 0} -> Int -> Float @-}
ex6 :: Float -> Int -> Float
ex6 x y = 1 / (x ^ y)
