module Test761 () where

import Language.Haskell.Liquid.Prelude

x = choose 0

prop_abs ::  Bool
prop_abs = if x > 0 then baz x else False

baz gooberding = liquidAssertB (gooberding >= 0)
