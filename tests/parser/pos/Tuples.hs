{-@ LIQUID "--exact-data-cons" @-}

module Tuples where

{-@ reflect f @-}
f :: Int -> Int
f x = x

{-@ reflect g @-}
g :: Int -> (Int, Int) -> (Int, Int)
g z (x, y) = (x, y)

{-@ reflect p @-}
p :: (Int, Int) -> Bool
p (x, y) = x == y

{-@ foo :: x:Int -> y:Int -> {z:Int | p (g z (f x, f y))} @-}
foo :: Int -> Int -> Int
foo x y = undefined
