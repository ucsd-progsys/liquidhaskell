module Foo where

data F = F {f1 :: Int, f2 :: Bool}

{-@ data F = F {f2 :: Bool, f1 :: Int} @-}
