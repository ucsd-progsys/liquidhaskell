module Inconsistent1 where

{-@ incr :: Int -> Bool @-}
incr :: Int -> Int 
incr x = x + 1
