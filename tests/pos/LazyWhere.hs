module LazyWhere () where

import Language.Haskell.Liquid.Prelude

{-@ pos :: Nat -> Int @-}
pos :: Int -> Int
pos = undefined


{-@ LAZYVAR z @-}
foo = if x > 0 then z else x
  where z = pos x
        x = choose 0
