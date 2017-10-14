module Hex where 

{-@ foo :: {x:Int | x = 0x7} -> {y:Int | y = 0x6} -> {v:Int | v = 0xF} @-}
foo :: Int -> Int -> Int 
foo x y = x + y


