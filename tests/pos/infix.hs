module Foo () where

import Language.Haskell.Liquid.Prelude (liquidAssert)

{-@ (!) :: zogbert:{v: Int | v > 0} -> {v: Int | v > 0} -> Int @-}
(!) :: Int -> Int -> Int
x ! y = x + y


{-@ (!!) :: {v: Int | v > 0} -> {v: Int | v > 0} -> Int @-}
(!!)   :: Int -> Int -> Int 
x !! y = liquidAssert (x /= 0) $ x + y 

{-@ zoo :: {v: Int | v > 0} -> {v: Int | v > 0} -> Int @-}
zoo   :: Int -> Int -> Int 
zoo x y = liquidAssert (x /= 0) $ x + y 


