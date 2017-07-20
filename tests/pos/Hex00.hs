module Hex where 

foo :: Int -> Int -> Int 
foo x y = x + y

{-@ foo :: {x:Int | x = 0x7} -> {y:Int | y = 0x8} -> {v:Int | v = 0xF} @-}

