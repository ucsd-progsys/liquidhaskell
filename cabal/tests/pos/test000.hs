module Test0 where

--import Language.Haskell.Liquid.Prelude

import Language.Haskell.Liquid.Prelude

x :: Int
x = choose 0

toss :: Bool
toss = x > 1000

prop_easy = if toss then assert toss else True
