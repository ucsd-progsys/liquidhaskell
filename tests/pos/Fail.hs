module Fail where 

{-@ fail incr @-}
{-@ incr :: x:Int -> {v:Int |  x < v } @-}
incr :: Int -> Int 
incr x = x 