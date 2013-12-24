module Holes where

{-@ foo :: x:_ -> y:{Int | y > 0} -> _ @-}
foo :: Int -> Int -> Int
foo x y = x

zero = foo 0 1
