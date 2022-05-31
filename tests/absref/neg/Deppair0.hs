{-@ LIQUID "--expect-any-error" @-}
module Deppair0 () where

import Language.Haskell.Liquid.Prelude

incr x = x + 1

baz x = (x, incr x)

prop :: Bool
prop = chk $ baz n
  where n = choose 100

chk (x, y) = liquidAssertB (x > y)

