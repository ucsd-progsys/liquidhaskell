module Test0 where

import LiquidPrelude

x = choose 0

prop_abs = if x > 0 then baz x else False

baz z = assert (z >= 10)
