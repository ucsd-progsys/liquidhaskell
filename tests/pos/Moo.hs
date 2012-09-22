module Moo (plusOne) where

{-@ assert plusOne :: x:Int -> {v:Int| v > x } @-}
plusOne :: Int -> Int
plusOne x = x + 1
