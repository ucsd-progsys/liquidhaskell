{-@ LIQUID "--expect-any-error" @-}
-- tests the "default method"

module Class01 where

{-@ class Foo a where
      foo :: a -> Nat
  @-}

class Foo a where
  foo :: a -> Int
  foo _ = 0 - 10
