module Poly0 (prop_id6) where

import Language.Haskell.Liquid.Prelude

myabs x    = if x `gt` 0 then x else 0 `minus` x

----------------------------------------------------------

myid3 x y  = y

prop_id6 x = liquidAssertB (x' `geq` 0)
  where x' = myid3 [] $ myabs x 


