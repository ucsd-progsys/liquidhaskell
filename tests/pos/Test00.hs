module Test00 () where

import Language.Haskell.Liquid.Prelude


prop_abs ::  Bool
prop_abs = if x > 0 then baz x else False
  where 
    x    = choose 0

baz gooberding = liquidAssertB (gooberding >= 0)
