module Class5 where

{-@ class Foo a where
      foo :: a -> Nat
  @-}

class Foo a where
  foo :: a -> Int
  foo _ = 0 - 10


