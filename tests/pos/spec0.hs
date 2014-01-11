module Test0 () where

import Language.Haskell.Liquid.Prelude

{-@ assert incr :: x:{v: Int | v >= 0} -> {v: Int | v > x} @-}
incr   :: Int -> Int
incr x = x + 1

myabs x = if x >= 0 then incr x else (0 - x)

prop_abs   = let n1 = choose 0 in 
             liquidAssertB ((myabs n1) >= 0)	
