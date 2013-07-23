module Test0 where

{-@ incr :: x:Int -> {v:Int | v > x} @-}
incr :: Int -> Int
incr x = x + 1

{- decr :: x:Int -> {v:Int | v < x} @-}
-- decr :: Int -> Int
-- decr x = x - 1
