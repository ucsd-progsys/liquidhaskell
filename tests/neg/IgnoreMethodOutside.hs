{-@ LIQUID "--expect-error-containing=Cannot ignore `m`" @-}
module IgnoreMethodOutside where

{-@ class MyClass a where
      m :: a -> {v:Int | v >= 1}
@-}
class MyClass a where
  m :: a -> Int

-- Error: cannot ignore a class method outside an instance
{-@ ignore m @-}

instance MyClass Int where
  m _x = 1
