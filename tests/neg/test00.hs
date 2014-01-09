module Test0 () where

import Language.Haskell.Liquid.Prelude

x = choose 0

prop_abs = if x > 0 then baz x else False

-- gob z = liquidAssertB (z `geq` 10)

baz z = liquidAssertB (z `geq` 100)
