module Fixme where

import Language.Haskell.Liquid.Prelude

foo = liquidAssert (w > 0)
   where w = 5 - 3
