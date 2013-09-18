module LazyWhere where

import Language.Haskell.Liquid.Prelude

{-@ pos :: Nat -> Int @-}
pos :: Int -> Int
pos = undefined

{-@ safeDiv :: Int -> {v:Int| v != 0} -> Int @-}
safeDiv :: Int -> Int -> Int
safeDiv = undefined


-- Limitations :: Definitions of lazy variables should be alpha renamed,
--  otherwise, internal variables will be created and the expression will be
--  unsafe

{-@ LAZYVAR z @-}
foo = if x > 0 then z else x
  where z  = (42 `safeDiv` x) + ( pos x)
        x = choose 0
