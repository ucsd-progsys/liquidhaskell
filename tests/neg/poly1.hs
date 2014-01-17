module Poly0 () where

import Language.Haskell.Liquid.Prelude

myabs x    = if x `gt` 0 then x else 0 `minus` x

myid2 a b  = a  

----------------------------------------------------------

x =  choose 0

prop_id4 = let x'  = myabs x in 
           let x'' = myid2 x' [] in 
           liquidAssertB (x'' `geq` 10)

prop_id5 = liquidAssertB (x'' `geq` 0)
  where x'  = myabs x 
        x'' = myid2 x' [] 
