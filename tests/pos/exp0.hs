
-- small test for playing around with exports.

module Moo (f) where

import Language.Haskell.Liquid.Prelude

data Goo = G Int

{-@ data Goo = G (x :: {v:Int | v > 0}) @-}

{-@ f :: Goo -> Goo @-} 
f (G n) 
  | n > 0     = G (n +  1)
  | otherwise = liquidError "ad"

