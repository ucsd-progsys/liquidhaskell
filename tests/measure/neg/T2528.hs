{-@ LIQUID "--expect-error-containing=is not a subtype of the required type" @-}
-- | Tests that the equations of an instance measure are used when the signature
-- of the measure contains type aliases.
module T2528 where

{-@ type List a = [a] @-}

{-@ class measure size :: forall f a. f a -> Nat @-}

{-@ instance measure size :: List a -> Nat
      size []     = 0
      size (x:xs) = 1 + (size xs)
  @-}

{-@ singleton :: a -> {v:[a] | size v = 2} @-}
singleton :: a -> [a]
singleton x = [x]
