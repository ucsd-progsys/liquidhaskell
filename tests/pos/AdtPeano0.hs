{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--higherorder"    @-}

module Peano where

-- | The code currently works if we add the below, but thats icky.
--   First, lets get this file to work _without_ the below.

{- data Influx = Silly Int @-}

data Influx = Silly Int

{-@ reflect thing @-}
thing :: Influx -> Int
thing (Silly a) = a + 1

{-@ reflect bling @-}
bling :: Influx -> Int
bling (Silly b) = b

{-@ test :: m:Influx -> { thing m = 1 + bling m} @-}
test :: Influx -> (Int, Int)
test m = (thing m, bling m)
