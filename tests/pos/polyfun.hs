module Poly4 () where

import Language.Haskell.Liquid.Prelude

foo :: a -> [Int]
foo f = [0]

prop  = all (\z -> liquidAssertB (z >= 0)) zs
          where zs = foo id 
