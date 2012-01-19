module Range where

import Control.Applicative
import LiquidPrelude

goo x = []

poo (x:_) = True
poo ([])  = assert False

xs = goo (choose 0)

prop1 = assert (poo xs)
