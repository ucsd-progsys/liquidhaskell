module Abs where

import Language.Haskell.Liquid.Prelude  (liquidAssert)

{-@ abz :: x:Int -> {v: Int | v >= 0} @-}
abz :: Int -> Int
abz x | x > 0     = x
      | otherwise = (0 - x)

{-@ prop_abz :: Int -> Int @-}
prop_abz z = liquidAssert (z' >= 0) z' 
  where z' = abz z

