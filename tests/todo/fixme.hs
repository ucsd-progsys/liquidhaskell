module Foo where

{-@ bar :: x:Int -> {v:Int | v < x } @-}
bar :: Int -> Int 
bar x = x 