module Crash where

class Foo a where
{-@ class Foo where
      foo :: x:a -> {v:a | v = x}
  @-}
  foo :: a -> a       


instance Foo Int where
  {-@ instance Foo Int where
       foo :: x:Int -> {v:Int | v = x + 1} @-}
  foo x = x + 1

instance Foo Integer where
  {-@ instance Foo Integer where
       foo :: x:Integer -> {v:Integer | v = x + 1} @-}
  foo x = x + 1

