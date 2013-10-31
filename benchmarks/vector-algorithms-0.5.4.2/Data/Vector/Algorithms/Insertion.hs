{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--no-termination" @-}
-- ---------------------------------------------------------------------------
-- |
-- Module      : Data.Vector.Algorithms.Insertion
-- Copyright   : (c) 2008-2010 Dan Doel
-- Maintainer  : Dan Doel
-- Stability   : Experimental
-- Portability : Portable
--
-- A simple insertion sort. Though it's O(n^2), its iterative nature can be
-- beneficial for small arrays. It is used to sort small segments of an array
-- by some of the more heavy-duty, recursive algorithms.

module Data.Vector.Algorithms.Insertion
       ( sort
       , sortBy
       , sortByBounds
       , sortByBounds'
       , Comparison
       ) where


import Prelude hiding (read, length)

import Control.Monad.Primitive

import Data.Vector.Generic.Mutable

import Data.Vector.Algorithms.Common (Comparison)

import qualified Data.Vector.Algorithms.Optimal as O

-- | Sorts an entire array using the default comparison for the type
{-@ sort :: (PrimMonad m, MVector v e, Ord e) => {v: (v (PrimState m) e) | 0 < (vsize v)} -> m () @-}
sort :: (PrimMonad m, MVector v e, Ord e) => v (PrimState m) e -> m ()
sort = sortBy  compare
{-# INLINABLE sort #-}

-- | Sorts an entire array using a given comparison
{-@ sortBy :: (PrimMonad m, MVector v e) => Comparison e -> {v: (v (PrimState m) e) | 0 < (vsize v)} -> m () @-}
sortBy :: (PrimMonad m, MVector v e) => Comparison e -> v (PrimState m) e -> m ()
sortBy cmp a = sortByBounds cmp a 0  (length a)
{-# INLINE sortBy #-}

-- | Sorts the portion of an array delimited by [l,u)
{-@ sortByBounds :: (PrimMonad m, MVector v e)
                 => Comparison e -> vec:(v (PrimState m) e) 
                -> l:(OkIdx vec) -> u:{v:Nat | (InRng v l (vsize vec))} 
                -> m ()
  @-}
sortByBounds :: (PrimMonad m, MVector v e)
             => Comparison e -> v (PrimState m) e -> Int -> Int -> m ()
sortByBounds cmp a l u
  | len < 2   = return ()
  | len == 2  = O.sort2ByOffset cmp a l
  | len == 3  = O.sort3ByOffset cmp a l
  | len == 4  = O.sort4ByOffset cmp a l
  | otherwise = O.sort4ByOffset cmp a l >> sortByBounds' cmp a l (l + 4) u
 where
 len = u - l
{-# INLINE sortByBounds #-}

-- | Sorts the portion of the array delimited by [l,u) under the assumption
-- that [l,m) is already sorted.
{-@ sortByBounds' :: (PrimMonad m, MVector v e)
                 => Comparison e -> vec:(v (PrimState m) e) 
                -> l:(OkIdx vec) 
                -> m:{v:Nat | (InRng v l (vsize vec))} 
                -> u:{v:Nat | (InRng v m (vsize vec))} 
                -> m ()
  @-}
sortByBounds' :: (PrimMonad m, MVector v e)
              => Comparison e -> v (PrimState m) e -> Int -> Int -> Int -> m ()
sortByBounds' cmp a l m u = sort (u - m) m
 where
 sort (twit :: Int) (i :: Int) 
   | i < u     = do v <- unsafeRead a i
                    insert cmp a l v i
                    sort (twit - 1) (i+1)
   | otherwise = return ()
{-# INLINE sortByBounds' #-}

-- Given a sorted array in [l,u), inserts val into its proper position,
-- yielding a sorted [l,u]
insert :: (PrimMonad m, MVector v e)
       => Comparison e -> v (PrimState m) e -> Int -> e -> Int -> m ()
insert cmp a l = loop
 where
 loop val j
   | j <= l    = unsafeWrite a l val
   | otherwise = do e <- unsafeRead a (j - 1)
                    case cmp val e of
                      LT -> unsafeWrite a j e >> loop val (j - 1)
                      _  -> unsafeWrite a j val
{-# INLINE insert #-}
