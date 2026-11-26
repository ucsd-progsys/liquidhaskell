-- | Tests that class measures and instance measures whose signatures contain
-- type aliases can be used in other modules.
module T2528Client where

import T2528

data Pair a = Pair a a

{-@ type PairOf a = Pair a @-}

{-@ instance measure size :: PairOf a -> Nat
      size (Pair x y) = 2
  @-}

{-@ pair :: a -> {v:Pair a | size v = 2} @-}
pair :: a -> Pair a
pair x = Pair x x

{-@ list :: a -> {v:[a] | size v = 1} @-}
list :: a -> [a]
list = singleton
