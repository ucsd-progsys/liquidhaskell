module Fixme where

{-@ plus :: a:Int -> b:Int -> {v:Int | v == a + b} @-}
plus :: Int -> Int -> Int
plus = (+)

one :: Int
one = 1

incr :: Int -> Int
incr x = x `plus` one

{-@ relational incr ~ incr :: x1:Int -> Int ~ x2:Int -> Int
                           | x1 < x2 => r1 x1 < r2 x2 @-}
