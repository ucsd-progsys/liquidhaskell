module T1709 where

{-@ incr :: x:Int -> {v:Int | x < v } @-}
incr :: Int -> Int 
incr x = x + 1

{-@ fail decr @-}
{-@ decr :: x:Int -> {v:Int | x < v } @-}
decr :: Int -> Int 
decr x = x - 1
