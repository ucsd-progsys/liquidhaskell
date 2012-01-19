module Test1 where

import LiquidPrelude

myabs x = if x `gt` 0 then x else 0 `minus` x

n = choose 0

prop_absf = assert ((myabs n) `geq` 4)
