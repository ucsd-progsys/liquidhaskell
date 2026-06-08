{-@ LIQUID "--expect-error-containing=Cannot ignore `helper`" @-}

-- | This module tests that the @ignore@ annotation only applies to methods of
-- the current class and not to other functions.
module IgnoreNonMethodInInstance where

{-@ class MyClass a where
      m :: a -> {v:Int | v >= 1}
@-}
class MyClass a where
  m :: a -> Int

{-@ helper :: Int -> Int @-}
helper :: Int -> Int
helper x = x

instance MyClass Int where
  {-@ ignore helper @-}
  m _x = 1
