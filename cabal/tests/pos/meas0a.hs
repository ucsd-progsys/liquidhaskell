module Range where

import Language.Haskell.Liquid.Prelude

goo x = let z = [x] in z

z0 _  = True
z1 _  = False

poo (x:_) = True 
poo ([])  = liquidAssert False 

xs = goo (choose 0)

prop0 = liquidAssert True 
prop1 = liquidAssert (poo xs)
