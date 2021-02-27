module Fixme where

{-@ add :: a:Int -> b:Int -> {v:Int | v == a + b} @-}
add :: Int -> Int -> Int
add = (+)

one :: Int
one = 1

idNum :: (Num a) => a -> a -> a
idNum _ x = x

idInt :: Int -> Int -> Int
idInt = idNum

incr :: Int -> Int
incr x = x `idInt` 0

{-@ relational incr ~ incr :: x1:Int -> Int ~ x2:Int -> Int
                           ~~ x1 < x2 => r1 x1 > r2 x2      @-}