module Poly4 () where

import Language.Haskell.Liquid.Prelude

x     = choose 0

baz y = y

prop  = liquidAssertB (baz True)
