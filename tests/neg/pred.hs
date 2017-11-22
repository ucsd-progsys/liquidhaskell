module Foo () where

{-@ predicate Gt X Y = (X < Y) @-}

{-@ incr :: x:Int -> {v:Int | Gt v x} @-}
incr :: Int -> Int
incr x = x + 1
