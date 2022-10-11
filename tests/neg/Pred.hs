{-@ LIQUID "--expect-any-error" @-}
module Pred () where

{-@ predicate Gt X Y = (X < Y) @-}

{-@ incr :: x:Int -> {v:Int | Gt v x} @-}
incr :: Int -> Int
incr x = x + 1
