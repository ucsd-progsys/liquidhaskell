module Range () where

import Control.Applicative
import Language.Haskell.Liquid.Prelude

goo x = [x]

xs = goo (choose 0)

nullity :: [a] -> Int
nullity []    = 0
nullity (x:_) = 1

prop2 = liquidAssertB (1 == nullity xs) 
