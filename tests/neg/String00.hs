{-@ LIQUID "--expect-any-error" @-}
module String00 () where

import Language.Haskell.Liquid.Prelude

foo = "dog"

prop1 = liquidAssertB (0 == 1)
prop2 = liquidAssertB (1 /= 1)
