module Foo where

{-@ LIQUID "--totality" @-}
bar :: Int -> Int -> Int
bar x y | x >  y = 1
        | x <= y = 0
