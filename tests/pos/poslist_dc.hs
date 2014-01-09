module Poslist () where

import Language.Haskell.Liquid.Prelude

myabs x    = if x `gt` 0 then x else 0 `minus` x
----------------------------------------------------------

checkPos [] = True
checkPos (z:zs) = liquidAssertB (z `geq` 0) &&  (checkPos zs)

xs   = [-100..100]
prop = checkPos $ map myabs xs
