{-# LANGUAGE KindSignatures #-}
{-@ LIQUID "--typeclass" @-}
module HK2 where

class HK (m :: * -> *) where
  {-@ lift :: x:a -> {v: (m a) | True } @-}
  lift :: a -> m a

