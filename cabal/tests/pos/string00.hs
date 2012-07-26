module Str0 where

import Language.Haskell.Liquid.Prelude

foo = "dog"

prop1 = liquidAssert (0 == 0)	
prop2 = liquidAssert (1 /= 0)
