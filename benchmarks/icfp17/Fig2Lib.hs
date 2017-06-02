
module Fig2Lib (inc, dec, idd) where

{-@ inc :: x:Int -> {v:Int | v = x+1} @-}
inc :: Int -> Int
inc x = x + 1

{-@ dec :: x:Int -> {v:Int | v = x-1} @-}
dec :: Int -> Int
dec x = x - 1

{-@ idd :: x:Int -> {v:Int | v = x} @-}
idd :: Int -> Int
idd z = z
