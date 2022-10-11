{-@ LIQUID "--expect-any-error" @-}
module Fail1 where

-- This should fail because the failing incr is SAFE 
{-@ fail incr @-}
{-@ incr :: x:Int -> {v:Int |  x < v } @-}
incr :: Int -> Int 
incr x = x + 1 
