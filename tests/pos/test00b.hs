module Test0 () where

import Language.Haskell.Liquid.Prelude

x = choose 0

foo x = x

prop_abs = if x > 0 then baz (foo x) else False

baz ::  (Num a, Ord a) => a -> Bool
baz z = liquidAssertB (z > 0)
