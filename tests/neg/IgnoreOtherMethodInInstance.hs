{-@ LIQUID "--expect-error-containing=Cannot ignore `m2`" @-}

-- | This module tests that the @ignore@ annotation only applies to methods of
-- the current class and not to other methods.
module IgnoreOtherMethodInInstance where

class MyClass a where
  m :: a -> Int

class MyClass2 a where
  m2 :: a -> Int

instance MyClass Int where
  {-@ ignore m2 @-}
  m _x = 1
