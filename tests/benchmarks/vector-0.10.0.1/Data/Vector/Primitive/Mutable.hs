{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables, DeriveDataTypeable, CPP #-}

-- |
-- Module      : Data.Vector.Primitive.Mutable
-- Copyright   : (c) Roman Leshchinskiy 2008-2010
-- License     : BSD-style
--
-- Maintainer  : Roman Leshchinskiy <rl@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable
-- 
-- Mutable primitive vectors.
--

module Data.Vector.Primitive.Mutable (
  -- * Mutable vectors of primitive types
  MVector(..), IOVector, STVector, Prim,

  -- * Accessors

  -- ** Length information
  length, null,

  -- ** Extracting subvectors
  slice, init, tail, take, drop, splitAt,
  unsafeSlice, unsafeInit, unsafeTail, unsafeTake, unsafeDrop,

  -- ** Overlapping
  overlaps,

  -- * Construction

  -- ** Initialisation
  new, unsafeNew, replicate, replicateM, clone,

  -- ** Growing
  grow, unsafeGrow,

  -- ** Restricting memory usage
  clear,

  -- * Accessing individual elements
  read, write, swap,
  unsafeRead, unsafeWrite, unsafeSwap,

  -- * Modifying vectors

  -- ** Filling and copying
  set, copy, move, unsafeCopy, unsafeMove
) where

import qualified Data.Vector.Generic.Mutable as G
import           Data.Primitive.ByteArray
import           Data.Primitive ( Prim, sizeOf )
import           Control.Monad.Primitive
import           Control.Monad ( liftM )

import Control.DeepSeq ( NFData )

import Prelude hiding ( length, null, replicate, reverse, map, read,
                        take, drop, splitAt, init, tail )

import Data.Typeable ( Typeable )

#include "../../../include/vector.h"

-- | Mutable vectors of primitive types.
data MVector s a = MVector {-# UNPACK #-} !Int
                           {-# UNPACK #-} !Int
                           {-# UNPACK #-} !(MutableByteArray s)
        -- deriving ( Typeable )

type IOVector = MVector RealWorld
type STVector s = MVector s

instance NFData (MVector s a)

instance Prim a => G.MVector MVector a where
  basicLength (MVector _ n _) = n
  basicUnsafeSlice j m (MVector i n arr)
    = MVector (i+j) m arr

  {-# INLINE basicOverlaps #-}
  basicOverlaps (MVector i m arr1) (MVector j n arr2)
    = sameMutableByteArray arr1 arr2
      && (between i j (j+n) || between j i (i+m))
    where
      between x y z = x >= y && x < z

  {-# INLINE basicUnsafeNew #-}
  basicUnsafeNew n = MVector 0 n
                     `liftM` newByteArray (n * sizeOf (undefined :: a))

  {-# INLINE basicUnsafeRead #-}
  basicUnsafeRead (MVector i n arr) j = readByteArray arr (i+j)

  {-# INLINE basicUnsafeWrite #-}
  basicUnsafeWrite (MVector i n arr) j x = writeByteArray arr (i+j) x

  {-# INLINE basicUnsafeCopy #-}
  basicUnsafeCopy (MVector i n dst) (MVector j _ src)
    = copyMutableByteArray dst (i*sz) src (j*sz) (n*sz)
    where
      sz = sizeOf (undefined :: a)
  
  {-# INLINE basicUnsafeMove #-}
  basicUnsafeMove (MVector i n dst) (MVector j _ src)
    = moveByteArray dst (i*sz) src (j*sz) (n * sz)
    where
      sz = sizeOf (undefined :: a)

  {-# INLINE basicSet #-}
  basicSet (MVector i n arr) x = setByteArray arr i n x

-- Length information
-- ------------------

-- | Length of the mutable vector.
{-@ length :: Prim v a => x:_ -> {v:Nat | v = (mvLen x)} @-}
length :: Prim a => MVector s a -> Int
{-# INLINE length #-}
length = G.length

-- | Check whether the vector is empty
{-@ null :: Prim v a => x:_ -> {v:Bool | ((Prop v) <=> (mvLen x) = 0)} @-}
null :: Prim a => MVector s a -> Bool
{-# INLINE null #-}
null = G.null

-- Extracting subvectors
-- ---------------------

-- | Yield a part of the mutable vector without copying it.
{-@ slice :: (Prim a) => i:Nat -> n:Nat -> {v:_ | (OkSlice v i n)} -> {v:_ | (mvLen v) = n} @-}
slice :: Prim a => Int -> Int -> MVector s a -> MVector s a
{-# INLINE slice #-}
slice = G.slice

take :: Prim a => Int -> MVector s a -> MVector s a
{-# INLINE take #-}
take = G.take

drop :: Prim a => Int -> MVector s a -> MVector s a
{-# INLINE drop #-}
drop = G.drop

splitAt :: Prim a => Int -> MVector s a -> (MVector s a, MVector s a)
{-# INLINE splitAt #-}
splitAt = G.splitAt

{-@ init :: (Prim a) => x:{_ | (mvLen x) > 0} -> {v:_ | (mvLen v) = (mvLen x) - 1} @-}
init :: Prim a => MVector s a -> MVector s a
{-# INLINE init #-}
init = G.init

{-@ tail :: (Prim a) => x:{_ | (mvLen x) > 0} -> {v:_ | (mvLen v) = (mvLen x) - 1} @-}
tail :: Prim a => MVector s a -> MVector s a
{-# INLINE tail #-}
tail = G.tail

-- | Yield a part of the mutable vector without copying it. No bounds checks
-- are performed.
{-@ unsafeSlice  :: (Prim a) => i:Nat -> n:Nat -> {v:_ | (OkSlice v i n)} -> {v:_ | (mvLen v) = n} @-}
unsafeSlice :: Prim a
            => Int  -- ^ starting index
            -> Int  -- ^ length of the slice
            -> MVector s a
            -> MVector s a
{-# INLINE unsafeSlice #-}
unsafeSlice = G.unsafeSlice

{-@ unsafeTake :: (Prim a) => n:Nat -> x:{_ | (HasN x n)} -> {v:_ | (mvLen v) = n} @-}
unsafeTake :: Prim a => Int -> MVector s a -> MVector s a
{-# INLINE unsafeTake #-}
unsafeTake = G.unsafeTake

{-@ unsafeDrop :: (Prim a) => n:Nat -> x:{_ | (HasN x n)} -> {v:_ | (mvLen v) = (mvLen x) - n} @-}
unsafeDrop :: Prim a => Int -> MVector s a -> MVector s a
{-# INLINE unsafeDrop #-}
unsafeDrop = G.unsafeDrop

{-@ unsafeInit :: (Prim a) => x:{_ | (mvLen x) > 0} -> {v:_ | (mvLen v)  = (mvLen x) - 1} @-}
unsafeInit :: Prim a => MVector s a -> MVector s a
{-# INLINE unsafeInit #-}
unsafeInit = G.unsafeInit

{-@ unsafeTail :: (Prim a) => x:{_ | (mvLen x) > 0} -> {v:_ | (mvLen v)  = (mvLen x) - 1} @-}
unsafeTail :: Prim a => MVector s a -> MVector s a
{-# INLINE unsafeTail #-}
unsafeTail = G.unsafeTail

-- Overlapping
-- -----------

-- Check whether two vectors overlap.
overlaps :: Prim a => MVector s a -> MVector s a -> Bool
{-# INLINE overlaps #-}
overlaps = G.overlaps

-- Initialisation
-- --------------

-- | Create a mutable vector of the given length.
{-@ new :: (PrimMonad m, Prim a) => n:Nat -> m (PVecN MVector m a n)  @-}
new :: (PrimMonad m, Prim a) => Int -> m (MVector (PrimState m) a)
{-# INLINE new #-}
new = G.new

-- | Create a mutable vector of the given length. The length is not checked.
{-@ unsafeNew :: (PrimMonad m, Prim a) => n:Nat -> m (PVecN MVector m a n)  @-}
unsafeNew :: (PrimMonad m, Prim a) => Int -> m (MVector (PrimState m) a)
{-# INLINE unsafeNew #-}
unsafeNew = G.unsafeNew

-- | Create a mutable vector of the given length (0 if the length is negative)
-- and fill it with an initial value.
{-@ replicate :: (PrimMonad m, Prim a) => n:Nat -> a -> m (PVecN MVector m a n) @-}
replicate :: (PrimMonad m, Prim a) => Int -> a -> m (MVector (PrimState m) a)
{-# INLINE replicate #-}
replicate = G.replicate

-- | Create a mutable vector of the given length (0 if the length is negative)
-- and fill it with values produced by repeatedly executing the monadic action.
{-@ replicateM :: (PrimMonad m, Prim a) => n:Nat -> m a -> m (PVecN MVector m a n) @-}
replicateM :: (PrimMonad m, Prim a) => Int -> m a -> m (MVector (PrimState m) a)
{-# INLINE replicateM #-}
replicateM = G.replicateM

-- | Create a copy of a mutable vector.
{-@ clone :: (PrimMonad m, Prim a) => x:(PVec MVector m a) -> m (PVecV MVector m a x) @-}
clone :: (PrimMonad m, Prim a)
      => MVector (PrimState m) a -> m (MVector (PrimState m) a)
{-# INLINE clone #-}
clone = G.clone

-- Growing
-- -------

-- | Grow a vector by the given number of elements. The number must be
-- positive.
{-@ grow :: (PrimMonad m, Prim a)
                => x:(PVec MVector m a) -> by:Nat -> m (PVecN MVector m a {(mvLen x) + by}) @-}
grow :: (PrimMonad m, Prim a)  
              => MVector (PrimState m) a -> Int -> m (MVector (PrimState m) a)
{-# INLINE grow #-}
grow = G.grow

-- | Grow a vector by the given number of elements. The number must be
-- positive but this is not checked.
{-@ unsafeGrow :: (PrimMonad m, Prim a) => x: (PVec MVector m a) -> n:Nat -> (m (PVecN MVector m a {(mvLen x) + n})) @-}
unsafeGrow :: (PrimMonad m, Prim a)
               => MVector (PrimState m) a -> Int -> m (MVector (PrimState m) a)
{-# INLINE unsafeGrow #-}
unsafeGrow = G.unsafeGrow

-- Restricting memory usage
-- ------------------------

-- | Reset all elements of the vector to some undefined value, clearing all
-- references to external objects. This is usually a noop for unboxed vectors. 
clear :: (PrimMonad m, Prim a) => MVector (PrimState m) a -> m ()
{-# INLINE clear #-}
clear = G.clear

-- Accessing individual elements
-- -----------------------------

-- | Yield the element at the given position.
{-@ read :: (PrimMonad m, Prim a) => x:(PVec MVector m a) -> (OkIx x) -> m a @-}
read :: (PrimMonad m, Prim a) => MVector (PrimState m) a -> Int -> m a
{-# INLINE read #-}
read = G.read

-- | Replace the element at the given position.
{-@ write :: (PrimMonad m, Prim a) => x:(PVec MVector m a) -> (OkIx x)-> a -> m () @-}
write :: (PrimMonad m, Prim a) => MVector (PrimState m) a -> Int -> a -> m ()
{-# INLINE write #-}
write = G.write

-- | Swap the elements at the given positions.
{-@ swap :: (PrimMonad m, Prim a) => x:(PVec MVector m a) -> (OkIx x) -> (OkIx x) -> m () @-}
swap :: (PrimMonad m, Prim a) => MVector (PrimState m) a -> Int -> Int -> m ()
{-# INLINE swap #-}
swap = G.swap


-- | Yield the element at the given position. No bounds checks are performed.
{-@ unsafeRead :: (PrimMonad m, Prim a) => x:(PVec MVector m a) -> (OkIx x) -> m a @-}
unsafeRead :: (PrimMonad m, Prim a) => MVector (PrimState m) a -> Int -> m a
{-# INLINE unsafeRead #-}
unsafeRead = G.unsafeRead

-- | Replace the element at the given position. No bounds checks are performed.
{-@ unsafeWrite :: (PrimMonad m, Prim a)
                                => x:(MVector (PrimState m) a) -> (OkIx x) -> a -> (m ()) @-}
unsafeWrite
    :: (PrimMonad m, Prim a) =>  MVector (PrimState m) a -> Int -> a -> m ()
{-# INLINE unsafeWrite #-}
unsafeWrite = G.unsafeWrite

-- | Swap the elements at the given positions. No bounds checks are performed.
{-@ unsafeSwap :: (PrimMonad m, Prim a)
                => x:(PVec MVector m a) -> (OkIx x) -> (OkIx x) -> m () @-}
unsafeSwap
    :: (PrimMonad m, Prim a) => MVector (PrimState m) a -> Int -> Int -> m ()
{-# INLINE unsafeSwap #-}
unsafeSwap = G.unsafeSwap

-- Filling and copying
-- -------------------

-- | Set all elements of the vector to the given value.
set :: (PrimMonad m, Prim a) => MVector (PrimState m) a -> a -> m ()
{-# INLINE set #-}
set = G.set

-- | Copy a vector. The two vectors must have the same length and may not
-- overlap.
{-@ copy :: (PrimMonad m, Prim a)
                => dst:(PVec MVector m a) -> src:(PVecV MVector m a dst) -> m () @-}
copy :: (PrimMonad m, Prim a) 
                 => MVector (PrimState m) a -> MVector (PrimState m) a -> m ()
{-# INLINE copy #-}
copy = G.copy

-- | Copy a vector. The two vectors must have the same length and may not
-- overlap. This is not checked.
{-@ unsafeCopy :: (PrimMonad m, Prim a)
               => dst:(PVec MVector m a) -> src:(PVecV MVector m a dst) -> m () @-}
unsafeCopy :: (PrimMonad m, Prim a)
           => MVector (PrimState m) a   -- ^ target
           -> MVector (PrimState m) a   -- ^ source
           -> m ()
{-# INLINE unsafeCopy #-}
unsafeCopy = G.unsafeCopy

-- | Move the contents of a vector. The two vectors must have the same
-- length.
-- 
-- If the vectors do not overlap, then this is equivalent to 'copy'.
-- Otherwise, the copying is performed as if the source vector were
-- copied to a temporary vector and then the temporary vector was copied
-- to the target vector.
{-@ move :: (PrimMonad m, Prim a)
                => dst:(PVec MVector m a) -> src:(PVecV MVector m a dst) -> m () @-}
move :: (PrimMonad m, Prim a)
                 => MVector (PrimState m) a -> MVector (PrimState m) a -> m ()
{-# INLINE move #-}
move = G.move

-- | Move the contents of a vector. The two vectors must have the same
-- length, but this is not checked.
-- 
-- If the vectors do not overlap, then this is equivalent to 'unsafeCopy'.
-- Otherwise, the copying is performed as if the source vector were
-- copied to a temporary vector and then the temporary vector was copied
-- to the target vector.
{-@ unsafeMove :: (PrimMonad m, Prim a) => dst:(PVec MVector m a)
                                             -> src:(PVecV MVector m a dst)
                                             -> m ()
  @-}
unsafeMove :: (PrimMonad m, Prim a)
                          => MVector (PrimState m) a   -- ^ target
                          -> MVector (PrimState m) a   -- ^ source
                          -> m ()
{-# INLINE unsafeMove #-}
unsafeMove = G.unsafeMove

