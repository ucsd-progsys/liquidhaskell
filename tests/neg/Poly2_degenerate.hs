{-@ LIQUID "--expect-any-error" @-}
module Poly2_degenerate () where

import Language.Haskell.Liquid.Prelude

myabs x    = if x `gt` 0 then x else 0 `minus` x

----------------------------------------------------------

myid3 x y  = y

prop_id6 = liquidAssertB (x' `geq` 10)
  where x' = myid3 [] $ myabs n 
        n  = choose 0

