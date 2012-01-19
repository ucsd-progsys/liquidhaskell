module Range where

import Control.Applicative
import Language.Haskell.Liquid.Prelude

--{-# ANN module "spec   $LIQUIDHS/List.spec" #-}
--{-# ANN module "hquals $LIQUIDHS/List.hquals" #-}

goo x = [x]

xs = goo (choose 0)

nullity :: [a] -> Int
nullity []    = 0
nullity (x:_) = 1

prop2 = assert (1 == nullity xs) 
