module TestRec where

import Language.Haskell.Liquid.Prelude


-- type signature should be there, otherwise games in Rec
-- bar1, bar2 :: (Eq k, Ord k) => k -> k -> k 
bar1 k v
  | k == v = bar2 k v
  | k <  v = k

bar2 k v
  | k == v = bar1 k v
  | k <  v = k


bar = bar1 1 1
