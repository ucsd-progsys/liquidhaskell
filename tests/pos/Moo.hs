module Moo (plusOne) where

{-@ plusOne :: x:Int -> {v:Int| 42 < v } @-}
plusOne :: Int -> Int
plusOne x = 43
