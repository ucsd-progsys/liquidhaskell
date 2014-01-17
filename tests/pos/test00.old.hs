module Test0 () where

import Language.Haskell.Liquid.Prelude

x = choose 0

prop_abs = if x `gt` 0 then baz x else False

baz   :: Int -> Bool
baz z = liquidAssertB (z `geq` 0)

