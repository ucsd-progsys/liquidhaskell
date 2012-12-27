module Fixme where

import Prelude hiding (length)
import Data.Vector
import Language.Haskell.Liquid.Prelude (liquidAssert)


{-@ foo :: x:(Vector Int) 
        -> y:{v: (Vector Int) | v = x } 
        -> Int 
  @-}
foo     :: Vector Int -> Vector Int -> Int
foo x y = liquidAssert (x == y) 0

{-@ bar :: x:Int 
        -> y:{v: Int | v = x } 
        -> Int 
  @-}
bar     :: Int -> Int -> Int
bar x y = liquidAssert (x == y) 0
