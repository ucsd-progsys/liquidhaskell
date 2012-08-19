module TestRec where

import Language.Haskell.Liquid.Prelude

bar1 k v
  | k == v = bar2 k v
  | k <  v = k

bar2 k v
  | k == v = bar1 k v
  | k <  v = k

bar = bar1 1 1
