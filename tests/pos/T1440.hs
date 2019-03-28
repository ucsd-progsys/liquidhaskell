module Hole where 

incr :: Int -> Int 
{-@ incr :: x:Int -> {v:Int | x < v } @-} 
incr = _incr 