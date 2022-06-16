{-# OPTIONS_GHC -Wno-missing-methods #-}
{-@ LIQUID "--expect-any-error" @-}
-- test noMethodBinding
module Total01 where

class Foo a where
  bar :: a -> a
  baz :: a -> a

instance Foo Int where
  bar x = x
