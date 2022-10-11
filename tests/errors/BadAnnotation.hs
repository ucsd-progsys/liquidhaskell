{-@ LIQUID "--expect-error-containing=Malformed annotation" @-}
module BadAnnotation where

{-@ incr :: x:Int -> {v:Int | x < v } -}
incr :: Int -> Int
incr x = x - 1
