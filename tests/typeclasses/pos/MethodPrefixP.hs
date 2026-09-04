-- Test that a class method whose name starts with 'p' is not mistaken for a
-- superclass dictionary binding: `$cpnat` must resolve to the method `pnat`,
-- not to a selector `$pnat`.
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}
module MethodPrefixP where

class PNum a where
  {-@ pnat :: a -> Nat @-}
  pnat :: a -> Int

instance PNum Bool where
  pnat False = 0
  pnat True  = 1
