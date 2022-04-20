-- TAG: reflect 

{-@ LIQUID "--reflection" @-}

module Ple00 where

{-@ reflect adder @-}
adder :: Int -> Int -> Int 
adder x y = x + y 

{-@ prop :: { v: Int | adder 5 6 == 11 } @-}
prop = adder 5 6  
