-- Test for issue #2727:
-- Specs of classes with higher-kinded parameters used to be elaborated with the
-- type application `m a` rendered as a function type `m -> a`, throwing a kind
-- error.

-- Unlike HK2, this test has an implicit higher kinded type.

{-@ LIQUID "--typeclass" @-}
module HK1 where

class M m where
  {-@ ret :: a -> m a @-}
  ret :: a -> m a

class M m => VM m where
  {-@ lawRet :: x:a -> y:m a ->
        { ((y == ret x) ==> (y == ret x)) && ((y == ret x) ==> (y == ret x)) } @-}
  lawRet :: a -> m a -> ()
