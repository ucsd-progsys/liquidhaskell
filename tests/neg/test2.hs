module Test1 () where

import Language.Haskell.Liquid.Prelude

myabs x = if x `gt` 0 then x else 0 `minus` x

n = choose 0

prop_absf = 
  let zz = (myabs n) `geq` 4 in
  liquidAssertB zz
