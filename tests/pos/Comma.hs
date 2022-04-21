module Comma where

{-@ measure mysnd @-}
mysnd :: (a, b) -> b
mysnd (_, y) = y

{-@ foo :: x:Int -> {v:Int | v == x} @-}
foo :: Int -> Int 
foo x = mysnd (x, x)

