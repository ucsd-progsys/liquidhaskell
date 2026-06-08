module IgnoreMethod where

class MyClass a where
  m :: a -> Int

instance MyClass Int where
  {-@ instance MyClass Int where
        m :: Int -> {v:Int | v >= 1}
    @-}
  {-@ ignore m @-}
  m _x = 0
