-- | Tests that type aliases can be used in the signatures of class measures and
-- instance measures.
module T2528 where

{-@ type List a = [a] @-}

{-@ class measure size :: forall f a. f a -> Nat @-}

{-@ instance measure size :: List a -> Nat
      size []     = 0
      size (x:xs) = 1 + (size xs)
  @-}

{-@ singleton :: a -> {v:[a] | size v = 1} @-}
singleton :: a -> [a]
singleton x = [x]
