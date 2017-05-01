{-# LANGUAGE CPP #-}

-- ---------------------------------------------------------------------------
-- |
-- Module      : Data.Vector.Algorithms.Optimal
-- Copyright   : (c) 2008-2010 Dan Doel
-- Maintainer  : Dan Doel
-- Stability   : Experimental
-- Portability : Portable
--
-- Optimal sorts for very small array sizes, or for small numbers of
-- particular indices in a larger array (to be used, for instance, for
-- sorting a median of 3 values into the lowest position in an array
-- for a median-of-3 quicksort).

-- The code herein was adapted from a C algorithm for optimal sorts
-- of small arrays. The original code was produced for the article
-- /Sorting Revisited/ by Paul Hsieh, available here:
--
--   http://www.azillionmonkeys.com/qed/sort.html
--
-- The LICENSE file contains the relevant copyright information for
-- the reference C code.

module Data.Vector.Algorithms.Optimal
       ( sort2ByIndex
       , sort2ByOffset
       , sort3ByIndex
       , sort3ByOffset
       , sort4ByIndex
       , sort4ByOffset
       , Comparison
       ) where

import Prelude hiding (read, length)

import Control.Monad.Primitive

import Data.Vector.Generic.Mutable

import Data.Vector.Algorithms.Common (Comparison)

-- LIQUID: seems to break compilation
#include "../../../include/vector.h"

-- | Sorts the elements at the positions 'off' and 'off + 1' in the given
-- array using the comparison.
{-@ sort2ByOffset 
      :: (PrimMonad m, MVector v e)
      => Comparison e -> vec:(v (PrimState m) e) -> {v:Nat | (OkRng v vec 1)} -> m ()
  @-}
sort2ByOffset :: (PrimMonad m, MVector v e)
              => Comparison e -> v (PrimState m) e -> Int -> m ()
sort2ByOffset cmp a off = sort2ByIndex cmp a off (off + 1)
{-# INLINABLE sort2ByOffset #-}

-- | Sorts the elements at the two given indices using the comparison. This
-- is essentially a compare-and-swap, although the first index is assumed to
-- be the 'lower' of the two.
{-@ sort2ByIndex
      :: (PrimMonad m, MVector v e)
      => Comparison e -> vec:(v (PrimState m) e) 
      -> {v:Nat | (OkRng v vec 0)} 
      -> {v:Nat | (OkRng v vec 0)} 
      -> m ()
  @-}
sort2ByIndex :: (PrimMonad m, MVector v e)
             => Comparison e -> v (PrimState m) e -> Int -> Int -> m ()
sort2ByIndex cmp a i j = UNSAFE_CHECK(checkIndex) "sort2ByIndex" i (length a)
                       $ UNSAFE_CHECK(checkIndex) "sort2ByIndex" j (length a)  $  do
  a0 <- unsafeRead a i
  a1 <- unsafeRead a j
  case cmp a0 a1 of
    GT -> unsafeWrite a i a1 >> unsafeWrite a j a0
    _  -> return ()
{-# INLINABLE sort2ByIndex #-}

-- | Sorts the three elements starting at the given offset in the array.
{-@ sort3ByOffset 
      :: (PrimMonad m, MVector v e)
      => Comparison e -> vec:(v (PrimState m) e) -> {v:Nat | (OkRng v vec 2)} -> m ()
  @-}
sort3ByOffset :: (PrimMonad m, MVector v e)
              => Comparison e -> v (PrimState m) e -> Int -> m ()
sort3ByOffset cmp a off = sort3ByIndex cmp a  off  (off + 1) (off + 2)
{-# INLINABLE sort3ByOffset #-}

-- | Sorts the elements at the three given indices. The indices are assumed
-- to be given from lowest to highest, so if 'l < m < u' then
-- 'sort3ByIndex cmp a m l u' essentially sorts the median of three into the
-- lowest position in the array.
{-@ sort3ByIndex
      :: (PrimMonad m, MVector v e)
      => Comparison e -> vec:(v (PrimState m) e) 
      -> {v:Nat | (OkRng v vec 0)} 
      -> {v:Nat | (OkRng v vec 0)} 
      -> {v:Nat | (OkRng v vec 0)}
      -> m ()
  @-}
sort3ByIndex :: (PrimMonad m, MVector v e)
             => Comparison e -> v (PrimState m) e -> Int -> Int -> Int -> m ()
sort3ByIndex cmp a i j k = UNSAFE_CHECK(checkIndex) "sort3ByIndex" i (length a)
                         $ UNSAFE_CHECK(checkIndex) "sort3ByIndex" j (length a)
                         $ UNSAFE_CHECK(checkIndex) "sort3ByIndex" k (length a) $ do
  a0 <- unsafeRead a i
  a1 <- unsafeRead a j
  a2 <- unsafeRead a k
  case cmp a0 a1 of
    GT -> case cmp a0 a2 of
            GT -> case cmp a2 a1 of
                    LT -> do unsafeWrite a i a2
                             unsafeWrite a k a0
                    _  -> do unsafeWrite a i a1
                             unsafeWrite a j a2
                             unsafeWrite a k a0
            _  -> do unsafeWrite a i a1
                     unsafeWrite a j a0
    _  -> case cmp a1 a2 of
            GT -> case cmp a0 a2 of
                    GT -> do unsafeWrite a i a2
                             unsafeWrite a j a0
                             unsafeWrite a k a1
                    _  -> do unsafeWrite a j a2
                             unsafeWrite a k a1
            _  -> return ()
{-# INLINABLE sort3ByIndex #-}

-- | Sorts the four elements beginning at the offset.
{-@ sort4ByOffset 
      :: (PrimMonad m, MVector v e)
      => Comparison e -> vec:(v (PrimState m) e) -> {v:Nat | (OkRng v vec 3)} -> m ()
  @-}
sort4ByOffset :: (PrimMonad m, MVector v e)
              => Comparison e -> v (PrimState m) e -> Int -> m ()
sort4ByOffset cmp a off = sort4ByIndex cmp a off (off + 1) (off + 2) (off + 3)
{-# INLINABLE sort4ByOffset #-}

-- The horror...

-- | Sorts the elements at the four given indices. Like the 2 and 3 element
-- versions, this assumes that the indices are given in increasing order, so
-- it can be used to sort medians into particular positions and so on.
{-@ sort4ByIndex
      :: (PrimMonad m, MVector v e)
      => Comparison e -> vec:(v (PrimState m) e) 
      -> {v:Nat | (OkRng v vec 0)} 
      -> {v:Nat | (OkRng v vec 0)} 
      -> {v:Nat | (OkRng v vec 0)} 
      -> {v:Nat | (OkRng v vec 0)} 
      -> m ()
  @-}
sort4ByIndex :: (PrimMonad m, MVector v e)
             => Comparison e -> v (PrimState m) e -> Int -> Int -> Int -> Int -> m ()
sort4ByIndex cmp a i j k l = UNSAFE_CHECK(checkIndex) "sort4ByIndex" i (length a)
                           $ UNSAFE_CHECK(checkIndex) "sort4ByIndex" j (length a)
                           $ UNSAFE_CHECK(checkIndex) "sort4ByIndex" k (length a)
                           $ UNSAFE_CHECK(checkIndex) "sort4ByIndex" l (length a) $ do
  a0 <- unsafeRead a i
  a1 <- unsafeRead a j
  a2 <- unsafeRead a k
  a3 <- unsafeRead a l
  case cmp a0 a1 of
    GT -> case cmp a0 a2 of
            GT -> case cmp a1 a2 of
                    GT -> case cmp a1 a3 of
                            GT -> case cmp a2 a3 of
                                    GT -> do unsafeWrite a i a3
                                             unsafeWrite a j a2
                                             unsafeWrite a k a1
                                             unsafeWrite a l a0
                                    _  -> do unsafeWrite a i a2
                                             unsafeWrite a j a3
                                             unsafeWrite a k a1
                                             unsafeWrite a l a0
                            _  -> case cmp a0 a3 of
                                    GT -> do unsafeWrite a i a2
                                             unsafeWrite a j a1
                                             unsafeWrite a k a3
                                             unsafeWrite a l a0
                                    _  -> do unsafeWrite a i a2
                                             unsafeWrite a j a1
                                             unsafeWrite a k a0
                                             unsafeWrite a l a3
                    _ -> case cmp a2 a3 of
                           GT -> case cmp a1 a3 of
                                   GT -> do unsafeWrite a i a3
                                            unsafeWrite a j a1
                                            unsafeWrite a k a2
                                            unsafeWrite a l a0
                                   _  -> do unsafeWrite a i a1
                                            unsafeWrite a j a3
                                            unsafeWrite a k a2
                                            unsafeWrite a l a0
                           _  -> case cmp a0 a3 of
                                   GT -> do unsafeWrite a i a1
                                            unsafeWrite a j a2
                                            unsafeWrite a k a3
                                            unsafeWrite a l a0
                                   _  -> do unsafeWrite a i a1
                                            unsafeWrite a j a2
                                            unsafeWrite a k a0
                                            -- unsafeWrite a l a3
            _  -> case cmp a0 a3 of
                    GT -> case cmp a1 a3 of
                            GT -> do unsafeWrite a i a3
                                     -- unsafeWrite a j a1
                                     unsafeWrite a k a0
                                     unsafeWrite a l a2
                            _  -> do unsafeWrite a i a1
                                     unsafeWrite a j a3
                                     unsafeWrite a k a0
                                     unsafeWrite a l a2
                    _  -> case cmp a2 a3 of
                            GT -> do unsafeWrite a i a1
                                     unsafeWrite a j a0
                                     unsafeWrite a k a3
                                     unsafeWrite a l a2
                            _  -> do unsafeWrite a i a1
                                     unsafeWrite a j a0
                                     -- unsafeWrite a k a2
                                     -- unsafeWrite a l a3
    _  -> case cmp a1 a2 of
            GT -> case cmp a0 a2 of
                    GT -> case cmp a0 a3 of
                            GT -> case cmp a2 a3 of
                                    GT -> do unsafeWrite a i a3
                                             unsafeWrite a j a2
                                             unsafeWrite a k a0
                                             unsafeWrite a l a1
                                    _  -> do unsafeWrite a i a2
                                             unsafeWrite a j a3
                                             unsafeWrite a k a0
                                             unsafeWrite a l a1
                            _  -> case cmp a1 a3 of
                                    GT -> do unsafeWrite a i a2
                                             unsafeWrite a j a0
                                             unsafeWrite a k a3
                                             unsafeWrite a l a1
                                    _  -> do unsafeWrite a i a2
                                             unsafeWrite a j a0
                                             unsafeWrite a k a1
                                             -- unsafeWrite a l a3
                    _  -> case cmp a2 a3 of
                            GT -> case cmp a0 a3 of
                                    GT -> do unsafeWrite a i a3
                                             unsafeWrite a j a0
                                             -- unsafeWrite a k a2
                                             unsafeWrite a l a1
                                    _  -> do -- unsafeWrite a i a0
                                             unsafeWrite a j a3
                                             -- unsafeWrite a k a2
                                             unsafeWrite a l a1
                            _  -> case cmp a1 a3 of
                                    GT -> do -- unsafeWrite a i a0
                                             unsafeWrite a j a2
                                             unsafeWrite a k a3
                                             unsafeWrite a l a1
                                    _  -> do -- unsafeWrite a i a0
                                             unsafeWrite a j a2
                                             unsafeWrite a k a1
                                             -- unsafeWrite a l a3
            _  -> case cmp a1 a3 of
                    GT -> case cmp a0 a3 of
                            GT -> do unsafeWrite a i a3
                                     unsafeWrite a j a0
                                     unsafeWrite a k a1
                                     unsafeWrite a l a2
                            _  -> do -- unsafeWrite a i a0
                                     unsafeWrite a j a3
                                     unsafeWrite a k a1
                                     unsafeWrite a l a2
                    _  -> case cmp a2 a3 of
                            GT -> do -- unsafeWrite a i a0
                                     -- unsafeWrite a j a1
                                     unsafeWrite a k a3
                                     unsafeWrite a l a2
                            _  -> do -- unsafeWrite a i a0
                                     -- unsafeWrite a j a1
                                     -- unsafeWrite a k a2
                                     -- unsafeWrite a l a3
                                     return ()
{-# INLINABLE sort4ByIndex #-}
