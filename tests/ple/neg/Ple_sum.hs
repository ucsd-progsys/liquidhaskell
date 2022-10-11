{-@ LIQUID "--expect-any-error" @-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--fuel=4" @-}

module Ple_sum where

{-@ reflect sumTo @-}
sumTo :: Int -> Int 
sumTo n = if n <= 0 then 0 else n + sumTo (n-1)

{-@ test :: () -> { sumTo 5 == 15 } @-}
test :: () -> () 
test _ = ()

