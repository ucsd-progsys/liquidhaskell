module Foo () where

import Language.Haskell.Liquid.Prelude (liquidAssert)

{-@ zoo :: {v: Int | v > 0} -> {v: Int | v > 0} -> Int @-}
zoo   :: Int -> Int -> Int 
zoo x y = liquidAssert (x /= 0) $ x + y 


foo = zoo (-1) (-2)

