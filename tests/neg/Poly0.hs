module Poly0 () where

import Language.Haskell.Liquid.Prelude

myabs x    = if x `gt` 0 then x else 0 `minus` x

myid arg     = arg

----------------------------------------------------------

x = choose 0

prop_id1 = let x'  = myabs x in 
           let x'' = myid x' in 
           liquidAssertB (x'' `geq` 0)

prop_id2 = liquidAssertB (x'' `geq` 0)
  where x'  = myabs x 
        x'' = myid x' 

prop_id3 = liquidAssertB (x' `geq` 20)
  where x' = myid $ myabs x 
