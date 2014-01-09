module Poly0 () where

import Language.Haskell.Liquid.Prelude

myabs x    = if x `gt` 0 then x else 0 `minus` x

----------------------------------------------------------

myid3 x y  = y

x = choose 0

prop_id6 = liquidAssertB (x' `geq` 10)
  where x' = myid3 [] $ myabs x 


