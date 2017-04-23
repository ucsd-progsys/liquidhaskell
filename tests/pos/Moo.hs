module Moo (plusOne) where

{-@ plusOne :: x:Int -> {v:Int| v = x + 1 } @-}
plusOne :: Int -> Int
plusOne x = x + 1
