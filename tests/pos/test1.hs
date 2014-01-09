module Test1 () where

import Language.Haskell.Liquid.Prelude

myabs x = if x > 0 then x else 0 - x

n = choose 0

prop_absf = liquidAssertB ((myabs n) >= 0)
