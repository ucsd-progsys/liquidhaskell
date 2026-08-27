-- Test for issue #2727:
-- Specs of classes with higher-kinded parameters used to be elaborated with the
-- type application `m a` rendered as a function type `m -> a`, throwing a kind
-- error.

-- Unlike HK1, this test has an explicit kind signature.

{-# LANGUAGE KindSignatures #-}
{-@ LIQUID "--typeclass" @-}
module HK2 where

import Data.Kind (Type)

class HK (m :: Type -> Type) where
  {-@ lift :: x:a -> {v: (m a) | True } @-}
  lift :: a -> m a
