module Assume where

{-@ assume incr :: Int -> {v : Int | v == x} @-}
incr :: Int -> Int
incr x = x + 1
