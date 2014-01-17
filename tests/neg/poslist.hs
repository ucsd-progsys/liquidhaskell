module Poslist () where

import Language.Haskell.Liquid.Prelude

myabs x    = if x `gt` 0 then x else 0 `minus` x

absList xs = map myabs xs

prop1 = map (liquidAssertB . (`geq` 0)) $ absList $ map choose [1..]


numAbs x   = if x > 0 then x else (x)

numAbsList = map numAbs 

prop2      = map (liquidAssertB . (>= 0)) $ numAbsList $ map choose [1..]
