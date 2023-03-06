module AbsPosTest where

{-@ f :: Int -> {n:Int | n >= 0} @-}
f :: Int -> Int
f x = abs x

{-@ g :: {n:Int | n >= 0} -> {m:Int | m = n} @-}
g :: Int -> Int
g x = abs x

{-@ h :: {n:Int | n < 0} -> {m:Int | m = -n} @-}
h :: Int -> Int
h x = abs x

{-@ f2 :: Int -> {n:Int | n >= 0} @-}
f2 :: Int -> Int
f2 x = abs x
