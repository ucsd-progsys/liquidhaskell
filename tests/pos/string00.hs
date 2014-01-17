module Str0 () where

import Language.Haskell.Liquid.Prelude

foo = "dog"

prop1 = liquidAssertB (0 == 0)	
prop2 = liquidAssertB (1 /= 0)
