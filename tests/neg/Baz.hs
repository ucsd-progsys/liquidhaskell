{-@ LIQUID "--short" @-}

module Baz where

{-@ incr :: x:Int -> {v:Int | v < x } @-}
incr   :: Int -> Int
incr x = id $ x + 1


{-@ iincr :: x:Int -> {v:Int | v < x } @-}
iincr   :: Int -> Int
iincr x = x + 1



