module B where

{-@ minus :: x:Int -> y:Int -> {v:Int | v = x - y} @-}
minus :: Int -> Int -> Int
minus x y = x - y

