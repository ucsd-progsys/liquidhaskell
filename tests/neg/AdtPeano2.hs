{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}

module Peano where

data Influx = Silly { goo :: Int }

test :: Int -> () 
test n = bob n (Silly n)

{-@ bob :: n:Int -> { v:Influx | v = Silly (n + 1) } -> () @-}
bob :: Int -> Influx -> () 
bob _ _ = () 
