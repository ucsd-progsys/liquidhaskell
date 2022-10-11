{-@ LIQUID "--expect-any-error" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Ple0 where

{-@ reflect adder @-}
adder :: Int -> Int -> Int 
adder x y = x + y 

{-@ prop :: { adder 5 6 == 12 } @-}
prop = ()
