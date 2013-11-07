{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- ---------------------------------------------------------------------------
-- |
-- Module      : Data.Vector.Algorithms.Search
-- Copyright   : (c) 2009-2010 Dan Doel
-- Maintainer  : Dan Doel <dan.doel@gmail.com>
-- Stability   : Experimental
-- Portability : Non-portable (bang patterns)
--
-- This module implements several methods of searching for indicies to insert
-- elements into a sorted vector.

module Data.Vector.Algorithms.Search
       ( binarySearch
       , binarySearchBy
       , binarySearchByBounds
       , binarySearchL
       , binarySearchLBy
       , binarySearchLByBounds
       , binarySearchR
       , binarySearchRBy
       , binarySearchRByBounds
       , Comparison
       ) where

import Prelude hiding (read, length)

import Control.Monad.Primitive

import Data.Bits

import Data.Vector.Generic.Mutable

import Data.Vector.Algorithms.Common (shiftRI, Comparison)

------------------------------------------------------------------------------------
-- LIQUID API Specifications -------------------------------------------------------
------------------------------------------------------------------------------------

{-@ binarySearch, binarySearchL, binarySearchR 
      :: (PrimMonad m, MVector v e, Ord e) 
      => vec:(v (PrimState m) e) -> e -> m (AOkIdx vec)
  @-}

{-@ binarySearchBy, binarySearchLBy, binarySearchRBy 
      :: (PrimMonad m, MVector v e) 
      => Comparison e -> vec:(v (PrimState m) e) -> e -> m (AOkIdx vec) 
  @-}

{-@ binarySearchByBounds, binarySearchLByBounds, binarySearchRByBounds 
      :: (PrimMonad m, MVector v e)
      => Comparison e -> vec:(v (PrimState m) e) -> e 
      -> l:{v:Nat | v <= (vsize vec)}
      -> u:{v:Nat | (l <= v && v <= (vsize vec))}
      -> m {v:Int | (l <= v && v <= u)}
  @-}


-------------------------------------------------------------------------------------

-- | Finds an index in a given sorted vector at which the given element could
-- be inserted while maintaining the sortedness of the vector.
binarySearch :: (PrimMonad m, MVector v e, Ord e)
             => v (PrimState m) e -> e -> m Int
binarySearch = binarySearchBy compare
{-# INLINE binarySearch #-}

-- | Finds an index in a given vector, which must be sorted with respect to the
-- given comparison function, at which the given element could be inserted while
-- preserving the vector's sortedness.
binarySearchBy :: (PrimMonad m, MVector v e)
               => Comparison e -> v (PrimState m) e -> e -> m Int
binarySearchBy cmp vec e = binarySearchByBounds cmp vec e 0 (length vec)
{-# INLINE binarySearchBy #-}

-- | Given a vector sorted with respect to a given comparison function in indices
-- in [l,u), finds an index in [l,u] at which the given element could be inserted
-- while preserving sortedness.
binarySearchByBounds :: (PrimMonad m, MVector v e)
                     => Comparison e -> v (PrimState m) e -> e -> Int -> Int -> m Int
binarySearchByBounds cmp vec e lo hi = loop (hi - lo) lo hi  
 where
 loop (twit :: Int) !l !u
   | u <= l    = return l
   | otherwise = do e' <- unsafeRead vec k
                    case cmp e' e of
                      LT -> loop (u - (k+1)) (k+1) u
                      EQ -> return  k
                      GT -> loop (k -l)      l     k
  where k = (u + l) `shiftRI` 1
{-# INLINE binarySearchByBounds #-}

{-@ smuggleQual :: twit:Nat -> l:Nat -> {v:Nat | v = l + twit} -> Int @-}
smuggleQual :: Int -> Int -> Int -> Int
smuggleQual = undefined

-- | Finds the lowest index in a given sorted vector at which the given element
-- could be inserted while maintaining the sortedness.
binarySearchL :: (PrimMonad m, MVector v e, Ord e) => v (PrimState m) e -> e -> m Int
binarySearchL = binarySearchLBy compare
{-# INLINE binarySearchL #-}

-- | Finds the lowest index in a given vector, which must be sorted with respect to
-- the given comparison function, at which the given element could be inserted
-- while preserving the sortedness.
binarySearchLBy :: (PrimMonad m, MVector v e)
                => Comparison e -> v (PrimState m) e -> e -> m Int
binarySearchLBy cmp vec e = binarySearchLByBounds cmp vec e 0 (length vec)
{-# INLINE binarySearchLBy #-}

-- | Given a vector sorted with respect to a given comparison function on indices
-- in [l,u), finds the lowest index in [l,u] at which the given element could be
-- inserted while preserving sortedness.
binarySearchLByBounds :: (PrimMonad m, MVector v e)
                      => Comparison e -> v (PrimState m) e -> e -> Int -> Int -> m Int
binarySearchLByBounds cmp vec e lo hi = loop (hi - lo) lo hi
 where
 loop (twit :: Int) !l !u
   | u <= l    = return l
   | otherwise = do e' <- unsafeRead vec k
                    case cmp e' e of
                      LT -> loop (u - (k+1)) (k+1) u
                      _  -> loop (k - l)     l     k
  where k = (u + l) `shiftRI` 1
{-# INLINE binarySearchLByBounds #-}

-- | Finds the greatest index in a given sorted vector at which the given element
-- could be inserted while maintaining sortedness.
binarySearchR :: (PrimMonad m, MVector v e, Ord e) => v (PrimState m) e -> e -> m Int
binarySearchR = binarySearchRBy compare
{-# INLINE binarySearchR #-}

-- | Finds the greatest index in a given vector, which must be sorted with respect to
-- the given comparison function, at which the given element could be inserted
-- while preserving the sortedness.
binarySearchRBy :: (PrimMonad m, MVector v e)
                => Comparison e -> v (PrimState m) e -> e -> m Int
binarySearchRBy cmp vec e = binarySearchRByBounds cmp vec e 0 (length vec)
{-# INLINE binarySearchRBy #-}

-- | Given a vector sorted with respect to the given comparison function on indices
-- in [l,u), finds the greatest index in [l,u] at which the given element could be
-- inserted while preserving sortedness.
binarySearchRByBounds :: (PrimMonad m, MVector v e)
                      => Comparison e -> v (PrimState m) e -> e -> Int -> Int -> m Int
binarySearchRByBounds cmp vec e lo hi = loop (hi - lo) lo hi
 where
 loop (twit :: Int) !l !u
   | u <= l    = return l
   | otherwise = do e' <- unsafeRead vec k
                    case cmp e' e of
                      GT -> loop (k - l)      l     k
                      _  -> loop (u - (k+1))  (k+1) u
  where k = (u + l) `shiftRI` 1
{-# INLINE binarySearchRByBounds #-}
