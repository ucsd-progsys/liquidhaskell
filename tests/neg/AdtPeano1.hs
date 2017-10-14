{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}

module Peano where

data Influx = Silly { goo :: Int }

{-@ test1:: n:Int -> m:Int -> { v:() | Silly n /= Silly m } -> { n == m } @-}
test1 :: Int -> Int -> () -> Int
test1 n m z = moo (Silly n) + moo (Silly m)

{-@ reflect moo @-}
moo :: Influx -> Int
moo (Silly a) = a
