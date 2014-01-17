module TopLevel where

import Language.Haskell.Liquid.Prelude

foo b = liquidAssertB b

bar = foo True
