-- positive tests for real exponentiation
module Foo where

{-@ ex1 :: Float -> Nat -> Float @-}
ex1 :: Float -> Int -> Float
ex1 x y = x ^ y

{-@ ex2 :: {n:Float | n /= 0} -> Nat -> Float @-}
ex2 :: Float -> Int -> Float
ex2 x y = 5 / (x ^ y)

{-@ ex3 :: Float -> {n:Nat | n == 0} -> {v:Float | v == 1} @-}
ex3 :: Float -> Int -> Float
ex3 x y = 1 / (x ^ y)

{-@ ex4 :: {b:Float | b == 0} -> {n:Nat | n /= 0} -> {v:Float | v == 0} @-}
ex4 :: Float -> Int -> Float
ex4 x y = x ^ y
