module Test0 () where

import Language.Haskell.Liquid.Prelude

x :: Int
x = choose 0

prop_abs ::  Bool
prop_abs = if x > 0 then baz x else False

baz :: Int -> Bool
baz gooberding = liquidAssertB (gooberding >= 0)
