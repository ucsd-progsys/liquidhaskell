module Foo where

import Control.Monad.Primitive

import Data.Vector.Generic.Mutable

{-@ copyOffset :: (PrimMonad m, MVector v e)
           => v (PrimState m) e -> v (PrimState m) e -> Int -> Int -> Int -> m ()
  @-}

copyOffset :: (PrimMonad m, MVector v e)
           => v (PrimState m) e -> v (PrimState m) e -> Int -> Int -> Int -> m ()
copyOffset = undefined

{-@ zog :: (m s a) -> Nat @-}
zog :: (m s a) -> Int
zog = undefined
