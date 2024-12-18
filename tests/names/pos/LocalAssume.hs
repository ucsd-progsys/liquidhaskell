-- | Tests that local assumptions are taken into consideration
module LocalAssume where

import Prelude (Int)

{-@ f :: {v: Int | v > 0} @-}
f :: Int
f = g
  where
    {-@ assume g :: {v:Int | v > 0} @-}
    g :: Int
    g = 0

