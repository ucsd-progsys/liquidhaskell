module Test0 () where

import Language.Haskell.Liquid.Prelude

myabs x = if x > 0 then x else (0 - x)

prop_abs   = let n1 = choose 0 in 
             liquidAssertB ((myabs n1) >= 0)
