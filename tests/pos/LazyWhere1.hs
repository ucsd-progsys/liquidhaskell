module LazyWhere () where

import Language.Haskell.Liquid.Prelude

{-@ pos :: Nat -> Int @-}
pos :: Int -> Int
pos = undefined

{-@ safeDiv :: Int -> {v:Int| v != 0} -> Int @-}
safeDiv :: Int -> Int -> Int
safeDiv = undefined

{-@ lazyvar z @-}
{-@ lazyvar z1 @-}
{-@ lazyvar z2 @-}
foo = if x > 0 then z else x
  where z  = z1 + z2
        z1 = 42 `safeDiv` x
        z2 = pos x
        x = choose 0
