module Test0 where

import Language.Haskell.Liquid.Prelude

toss :: Bool 
toss = (choose 0) > 10

prop_abs :: Bool
prop_abs = if toss then (if toss then assert toss else False) else False

