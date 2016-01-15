module Main where

{-@ LIQUID "--real" @-}

{-@ search :: { hi : Int | 0 < hi } -> Int @-}
search :: Int -> Int
search hi = search (hi `div` 2)

