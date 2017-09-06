module Zoo where

{-@ incr :: x:Int 
         -> {v:Int | x < v } 
  -}
incr :: Int -> Int
incr x = x - 1
