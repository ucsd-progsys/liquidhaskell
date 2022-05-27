-- tests ple+reflection

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Ple01 where

{-@ reflect adder @-}
adder :: Int -> Int -> Int 
adder x y = x + y 

{-@ prop :: { v: () | adder 5 6 == 11 } @-}
prop = ()
