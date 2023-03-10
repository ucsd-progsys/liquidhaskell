{-@ LIQUID "--expect-error-containing=Exponential1NegTest.hs:5:1" @-}
module Exponential1NegTest where

ex5 :: Float -> Int -> Float
ex5 x y = x ^ y
