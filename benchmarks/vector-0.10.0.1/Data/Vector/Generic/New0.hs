{-# LANGUAGE Rank2Types, FlexibleContexts #-}

-- |
-- Module      : Data.Vector.Generic.New
-- Copyright   : (c) Roman Leshchinskiy 2008-2010
-- License     : BSD-style
--
-- Maintainer  : Roman Leshchinskiy <rl@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable
--
-- Purely functional interface to initialisation of mutable vectors
--
{-@ LIQUID "--short-names" @-}

module Data.Vector.Generic.New (
  transform
) where

import Language.Haskell.Liquid.Prelude (liquidAssert)
import           Data.Vector.Generic.Mutable ( MVector )
import           Data.Vector.Generic.Base (Vector, Mutable )
import           Data.Vector.Fusion.Stream (MStream )

import Control.Monad.Primitive
import Control.Monad.ST ( ST )

{-@ data New v a = New (nn :: (forall s. ST s {z:(Mutable v s a) | 0 <= (mvLen z)})) @-}
data New v a = New (forall s. ST s (Mutable v s a))

transform :: Vector v a =>
        (forall m. Monad m => MStream m a -> MStream m a) -> New v a -> New v a
transform f (New poing) = New $ do zog <- poing
                                   let fef =  liquidAssert (0 <= flerp zog) zog
                                   goober f fef

{-@ flerp :: x:a -> {v:Int | v = (mvLen x)} @-}
flerp :: a -> Int
flerp = undefined

{-@ goober :: (PrimMonad m, MVector v a)
      => (MStream m a -> MStream m a) -> (PVec v m a) -> m (PVec v m a) @-}
goober :: (PrimMonad m, MVector v a)
  => (MStream m a -> MStream m a) -> v (PrimState m) a -> m (v (PrimState m) a)
goober = undefined
