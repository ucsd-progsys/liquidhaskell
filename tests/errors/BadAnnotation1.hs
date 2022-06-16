{-@ LIQUID "--expect-error-containing=Malformed annotation" @-}
module BadAnnotation1 where

{-@ incr :: x:Int 
         -> {v:Int | x < v } 
  -}
incr :: Int -> Int
incr x = x - 1
