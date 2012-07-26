module Range where

import Control.Applicative
import Language.Haskell.Liquid.Prelude

goo x = []

poo (x:_) = True
poo ([])  = liquidAssert False

xs = goo (choose 0)

prop1 = liquidAssert (poo xs)
