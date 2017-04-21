module Moo (plusOne) where

{-@ plusOne :: x:Int -> {v:Int| v > x } @-}
plusOne :: Int -> Int
plusOne x = x + 1
