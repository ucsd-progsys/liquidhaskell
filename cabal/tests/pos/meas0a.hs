module Range where

import Language.Haskell.Liquid.Prelude

--{-# ANN module "spec   $LIQUIDHS/List.spec" #-}
--{-# ANN module "hquals $LIQUIDHS/List.hquals" #-}

goo x = let z = [x] in z

z0 _  = True
z1 _  = False

poo (x:_) = True 
poo ([])  = assert False 

xs = goo (choose 0)

prop0 = assert True 
prop1 = assert (poo xs)
