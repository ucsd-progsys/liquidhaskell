module Range () where

import Language.Haskell.Liquid.Prelude

goo x = let z = [x] in z

z0 _  = True
z1 _  = False

poo (x:_) = True 
poo ([])  = liquidAssertB False 

xs = goo (choose 0)

prop0 = liquidAssertB True 
prop1 = liquidAssertB (poo xs)
