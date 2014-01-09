module Foo () where

{-@ predicate Gt x y = (x < y) @-}

{- incr :: x:Int -> {v:Int | v > x} @-}
{-@ incr :: x:Int -> {v:Int | (Gt v x)} @-}
incr :: Int -> Int
incr x = x + 1
