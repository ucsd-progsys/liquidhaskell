{-@ LIQUID "--short" @-}

module Baz where

{-@ incr :: x:Int -> {v:Int | v < x } @-}
incr   :: Int -> Int
incr xana = id $ xana + 1


{-@ iincr :: x:Int -> {v:Int | v < x } @-}
iincr   :: Int -> Int
iincr x = x + 1



