{-# LANGUAGE TypeOperators, BangPatterns, ScopedTypeVariables #-}

-- ---------------------------------------------------------------------------
-- |
-- Module      : Data.Vector.Algorithms.Intro
-- Copyright   : (c) 2008-2011 Dan Doel
-- Maintainer  : Dan Doel <dan.doel@gmail.com>
-- Stability   : Experimental
-- Portability : Non-portable (type operators, bang patterns)
--
-- This module implements various algorithms based on the introsort algorithm,
-- originally described by David R. Musser in the paper /Introspective Sorting
-- and Selection Algorithms/. It is also in widespread practical use, as the
-- standard unstable sort used in the C++ Standard Template Library.
--
-- Introsort is at its core a quicksort. The version implemented here has the
-- following optimizations that make it perform better in practice:
--
--   * Small segments of the array are left unsorted until a final insertion
--     sort pass. This is faster than recursing all the way down to
--     one-element arrays.
--
--   * The pivot for segment [l,u) is chosen as the median of the elements at
--     l, u-1 and (u+l)/2. This yields good behavior on mostly sorted (or
--     reverse-sorted) arrays.
--
--   * The algorithm tracks its recursion depth, and if it decides it is
--     taking too long (depth greater than 2 * lg n), it switches to a heap
--     sort to maintain O(n lg n) worst case behavior. (This is what makes the
--     algorithm introsort).

module Data.Vector.Algorithms.Intro
       ( -- * Sorting
         sort
       , sortBy
       , sortByBounds
         -- * Selecting
       , select
       , selectBy
       , selectByBounds
         -- * Partial sorting
       , partialSort
       , partialSortBy
       , partialSortByBounds
       , Comparison
       ) where

import Prelude hiding (read, length)

import Control.Monad
import Control.Monad.Primitive

import Data.Bits
import Data.Vector.Generic.Mutable

import Data.Vector.Algorithms.Common (Comparison)

import qualified Data.Vector.Algorithms.Insertion as I
import qualified Data.Vector.Algorithms.Optimal   as O
import qualified Data.Vector.Algorithms.Heap      as H

-- | Sorts an entire array using the default ordering.
sort :: (PrimMonad m, MVector v e, Ord e) => v (PrimState m) e -> m ()
sort = sortBy compare
{-# INLINABLE sort #-}

-- | Sorts an entire array using a custom ordering.
sortBy :: (PrimMonad m, MVector v e) => Comparison e -> v (PrimState m) e -> m ()
sortBy cmp a = sortByBounds cmp a 0 (length a)
{-# INLINE sortBy #-}

-- | Sorts a portion of an array [l,u) using a custom ordering
sortByBounds :: (PrimMonad m, MVector v e)
             => Comparison e -> v (PrimState m) e -> Int -> Int -> m ()
sortByBounds cmp a l u
  | len < 2   = return ()
  | len == 2  = O.sort2ByOffset cmp a l
  | len == 3  = O.sort3ByOffset cmp a l
  | len == 4  = O.sort4ByOffset cmp a l
  | otherwise = introsort cmp a (ilg len) l u
 where len = u - l
{-# INLINE sortByBounds #-}

-- Internal version of the introsort loop which allows partial
-- sort functions to call with a specified bound on iterations.
introsort :: (PrimMonad m, MVector v e)
          => Comparison e -> v (PrimState m) e -> Int -> Int -> Int -> m ()
introsort cmp a i l u = sort i l u >> I.sortByBounds cmp a l u
 where
 sort 0 l u = H.sortByBounds cmp a l u
 sort d l u
   | len < threshold = return ()
   | otherwise = do O.sort3ByIndex cmp a c l (u-1) -- sort the median into the lowest position
                    p <- unsafeRead a l
                    mid <- partitionBy cmp a p (l+1) u
                    unsafeSwap a l (mid - 1)
                    sort (d-1) mid u
                    sort (d-1) l   (mid - 1)
  where
  len = u - l
  c   = (u + l) `div` 2
{-# INLINE introsort #-}

-- | Moves the least k elements to the front of the array in
-- no particular order.
select :: (PrimMonad m, MVector v e, Ord e) => v (PrimState m) e -> Int -> m ()
select = selectBy compare
{-# INLINE select #-}

-- | Moves the least k elements (as defined by the comparison) to
-- the front of the array in no particular order.
selectBy :: (PrimMonad m, MVector v e)
         => Comparison e -> v (PrimState m) e -> Int -> m ()
selectBy cmp a k = selectByBounds cmp a k 0 (length a)
{-# INLINE selectBy #-}

-- | Moves the least k elements in the interval [l,u) to the positions
-- [l,k+l) in no particular order.
selectByBounds :: (PrimMonad m, MVector v e)
               => Comparison e -> v (PrimState m) e -> Int -> Int -> Int -> m ()
selectByBounds cmp a k l u
  | l >= u    = return ()
  | otherwise = go (ilg len) l (l + k) u
 where
 len = u - l
 go 0 l m u = H.selectByBounds cmp a (m - l) l u
 go n l m u = do O.sort3ByIndex cmp a c l (u-1)
                 p <- unsafeRead a l
                 mid <- partitionBy cmp a p (l+1) u
                 unsafeSwap a l (mid - 1)
                 if m > mid
                   then go (n-1) mid m u
                   else if m < mid - 1
                        then go (n-1) l m (mid - 1)
                        else return ()
  where c = (u + l) `div` 2
{-# INLINE selectByBounds #-}

-- | Moves the least k elements to the front of the array, sorted.
partialSort :: (PrimMonad m, MVector v e, Ord e) => v (PrimState m) e -> Int -> m ()
partialSort = partialSortBy compare
{-# INLINE partialSort #-}

-- | Moves the least k elements (as defined by the comparison) to
-- the front of the array, sorted.
partialSortBy :: (PrimMonad m, MVector v e)
              => Comparison e -> v (PrimState m) e -> Int -> m ()
partialSortBy cmp a k = partialSortByBounds cmp a k 0 (length a)
{-# INLINE partialSortBy #-}

-- | Moves the least k elements in the interval [l,u) to the positions
-- [l,k+l), sorted.
partialSortByBounds :: (PrimMonad m, MVector v e)
                    => Comparison e -> v (PrimState m) e -> Int -> Int -> Int -> m ()
partialSortByBounds cmp a k l u
  | l >= u    = return ()
  | otherwise = go (ilg len) l (l + k) u
 where
 isort = introsort cmp a
 {-# INLINE [1] isort #-}
 len = u - l
 go 0 l m n = H.partialSortByBounds cmp a (m - l) l u
 go n l m u
   | l == m    = return ()
   | otherwise = do O.sort3ByIndex cmp a c l (u-1)
                    p <- unsafeRead a l
                    mid <- partitionBy cmp a p (l+1) u
                    unsafeSwap a l (mid - 1)
                    case compare m mid of
                      GT -> do isort (n-1) l (mid - 1)
                               go (n-1) mid m u
                      EQ -> isort (n-1) l m
                      LT -> go n l m (mid - 1)
  where c = (u + l) `div` 2
{-# INLINE partialSortByBounds #-}

partitionBy :: forall m v e. (PrimMonad m, MVector v e)
            => Comparison e -> v (PrimState m) e -> e -> Int -> Int -> m Int
partitionBy cmp a = partUp
 where
 -- 6.10 panics without the signatures for partUp and partDown, 6.12 and later
 -- versions don't need them
 partUp :: e -> Int -> Int -> m Int
 partUp p l u
   | l < u = do e <- unsafeRead a l
                case cmp e p of
                  LT -> partUp p (l+1) u
                  _  -> partDown p l (u-1)
   | otherwise = return l

 partDown :: e -> Int -> Int -> m Int
 partDown p l u
   | l < u = do e <- unsafeRead a u
                case cmp p e of
                  LT -> partDown p l (u-1)
                  _  -> unsafeSwap a l u >> partUp p (l+1) u
   | otherwise = return l
{-# INLINE partitionBy #-}

-- computes the number of recursive calls after which heapsort should
-- be invoked given the lower and upper indices of the array to be sorted
ilg :: Int -> Int
ilg m = 2 * loop m 0
 where
 loop 0 !k = k - 1
 loop n !k = loop (n `shiftR` 1) (k+1)

-- the size of array at which the introsort algorithm switches to insertion sort
threshold :: Int
threshold = 18
{-# INLINE threshold #-}
