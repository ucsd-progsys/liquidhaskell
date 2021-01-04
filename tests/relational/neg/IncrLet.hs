module Fixme where

incr :: Int -> Int
incr = let one = 1 in (+ one)

{-@ relational incr ~ incr :: x1:Int -> Int ~ x2:Int -> Int
                           ~~ x1 < x2 => r1 x1 > r2 x2      @-}
