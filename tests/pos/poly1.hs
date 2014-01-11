module Poly0 () where

import Language.Haskell.Liquid.Prelude

myabs x    = if x > 0 then x else (0 - x)

myid2 a b  = a  

----------------------------------------------------------

x =  choose 0

prop_id4 = let x'  = myabs x in 
           let x'' = myid2 x' [] in 
           liquidAssertB (x'' >= 0) 

prop_id5 = liquidAssertB (x'' >= 0)
  where x'  = myabs x 
        x'' = myid2 x' [] 
