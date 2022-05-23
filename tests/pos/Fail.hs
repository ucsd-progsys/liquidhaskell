module Fail where

{-@ fail incr @-}
{-@ incr :: x:Int -> {v:Int |  x < v } @-}
incr :: Int -> Int 
incr x = x 

{-@ fail unsafe @-}
{-@ unsafe :: () -> { 0 == 1 } @-}
unsafe :: () -> () 
unsafe _ = () 
