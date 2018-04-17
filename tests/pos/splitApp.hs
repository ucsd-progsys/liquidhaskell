module SplitApp where

{-@ f :: u:Int -> w:Int -> {v:Int|v=u+w} @-}
f :: Int -> Int -> Int
f a b = a + b

{-@ g :: j:Int -> Int -> Int -> {v:Int|v=j} @-}
g :: Int -> Int -> Int -> Int
g x y z = f x y - y
