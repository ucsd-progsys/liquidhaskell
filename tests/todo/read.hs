module Read where

import Language.Haskell.Liquid.Prelude

data Foo = Foo deriving Read

bad  = liquidAssertB (0 == 1)
bad' = liquidAssert  (0 == 1) True
