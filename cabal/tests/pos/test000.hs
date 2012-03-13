module Test0 where

--import Language.Haskell.Liquid.Prelude

import Language.Haskell.Liquid.Prelude

x :: Int
x = choose 0

baz :: Int -> Bool
baz gooberding = assert (gooberding >= 0)

prop_abs ::  Bool
prop_abs = if x > 0 then baz x else False
