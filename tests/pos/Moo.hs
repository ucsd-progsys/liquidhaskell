module Moo (plusOne) where

{-@ plusOne :: x:Int -> {v:Int| 43 =  v } @-}
plusOne :: Int -> Int
plusOne x = 43
