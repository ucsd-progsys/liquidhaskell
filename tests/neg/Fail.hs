{-@ LIQUID "--expect-any-error" @-}
module Fail where

{-@ fail incr @-}
{-@ incr :: x:Int -> {v:Int |  x < v } @-}
incr :: Int -> Int 
incr x = x 


-- This should fails because the failing incr is used 
{-@ incr2 :: x:Int -> {v:Int | x < v } @-}
incr2 :: Int -> Int 
incr2 x = incr (incr x)
