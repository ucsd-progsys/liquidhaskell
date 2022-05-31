{-@ LIQUID "--expect-any-error" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Ple1Lib where

{-@ reflect adder @-}
adder :: Int -> Int -> Int 
adder x y = x + y 

{-@ prop :: _ -> { adder 5 6 == 12 } @-}
prop () = ()
