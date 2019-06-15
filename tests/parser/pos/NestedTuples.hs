{-@ LIQUID "--exact-data-cons" @-}

module NestedTuples where

{-@ reflect f @-}
f :: Int -> Int
f x = x

{-@ reflect g @-}
g :: Int -> (Int, (Bool, Int)) -> (Int, Int)
g z (x, (t, y)) = (if t then x else y, y)

{-@ reflect p @-}
p :: (Int, Int) -> Bool
p (x, y) = x == y

{-@ foo :: x:Int -> y:Int -> {z:Int | p (g z (f x, (true, f y)))} @-}
foo :: Int -> Int -> Int
foo x y = undefined
