module Poly0 where

import LiquidPrelude

myabs x    = if x `gt` 0 then x else 0 `minus` x

----------------------------------------------------------

myid3 x y  = y

x = choose 0

prop_id6 = assert (x' `geq` 10)
  where x' = myid3 [] $ myabs x 


