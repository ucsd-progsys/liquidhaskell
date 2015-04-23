module Foo () where

{-@ LIQUID "--diff"           @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

baz = bob 10

bob :: Int -> Int
bob x = x
