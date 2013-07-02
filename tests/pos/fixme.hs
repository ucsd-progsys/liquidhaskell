module Fixme where

import Language.Haskell.Liquid.Prelude

bar :: Int -> Int
-- bar 0 = 0
bar n = bar (n-1)


foo = bar n
  where n = choose 0
