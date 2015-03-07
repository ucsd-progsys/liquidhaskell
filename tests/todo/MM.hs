module MM where

import LL

{-@ bar :: x:Int -> {v:Int | v > 100 } @-}
bar :: Int -> Int
bar x = foo x
