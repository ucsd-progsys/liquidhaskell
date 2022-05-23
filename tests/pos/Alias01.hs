module Alias01 () where

{-@ type GeNum a N = {v: a | N <= v} @-}

{-@ type PosInt = GeNum Int {0} @-}

{-@ myabs :: Int -> PosInt @-}
myabs :: Int -> Int
myabs x = if (x > 0) then x else (0 - x)

{-@ incr :: x:Int -> GeNum Int {x} @-}
incr :: Int -> Int
incr x = x + 1

