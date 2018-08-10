module Incr where 

{-@ incr :: x:Int -> {v:Int | v > x} @-}
incr :: Int -> Int 
incr x = x + 1

