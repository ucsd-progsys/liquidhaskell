module Test0 where

--import Language.Haskell.Liquid.Prelude

import Language.Haskell.Liquid.Prelude

toss :: Bool 
toss = (choose 0) > 10

--baz gooberding = assert gooberding

prop_abs :: Bool
prop_abs = if toss then assert toss else False
