module Foo where

{-@ predicate Lt x y = x < y @-}
{-@ predicate Ge x y = not (Lt x y) @-}
{-@ predicate Pos x  = x > 0 @-}

{-@ incr :: x:{v:Int | (Pos v)} -> { v:Int | ((Pos v) && (Ge v x))} @-}
incr :: Int -> Int
incr x = x + 1
