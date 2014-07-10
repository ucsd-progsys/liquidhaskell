{-@ LIQUID "--short" @-}

module Baz where

{-@ incr :: x:Int -> {v:Int | v < x } @-}
incr   :: Int -> Int
incr x = id $ x + 1


