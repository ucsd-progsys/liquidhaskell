module MM where

import LL

{-@ bar :: x:Int -> {v:Int | v > x} @-}
bar :: Int -> Int
bar x = foo x
