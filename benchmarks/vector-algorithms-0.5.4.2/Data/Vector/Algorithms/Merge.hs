-- ---------------------------------------------------------------------------
-- |
-- Module      : Data.Vector.Algorithms.Merge
-- Copyright   : (c) 2008-2011 Dan Doel
-- Maintainer  : Dan Doel <dan.doel@gmail.com>
-- Stability   : Experimental
-- Portability : Portable
--
-- This module implements a simple top-down merge sort. The temporary buffer
-- is preallocated to 1/2 the size of the input array, and shared through
-- the entire sorting process to ease the amount of allocation performed in
-- total. This is a stable sort.

module Data.Vector.Algorithms.Merge
       ( sort
       , sortBy
       , Comparison
       ) where

import Prelude hiding (read, length)

import Control.Monad.Primitive

import Data.Bits
import Data.Vector.Generic.Mutable

import Data.Vector.Algorithms.Common (Comparison, copyOffset)

import qualified Data.Vector.Algorithms.Optimal   as O
import qualified Data.Vector.Algorithms.Insertion as I

-- | Sorts an array using the default comparison.
sort :: (PrimMonad m, MVector v e, Ord e) => v (PrimState m) e -> m ()
sort = sortBy compare
{-# INLINABLE sort #-}

-- | Sorts an array using a custom comparison.
sortBy :: (PrimMonad m, MVector v e) => Comparison e -> v (PrimState m) e -> m ()
sortBy cmp vec
  | len <= 1  = return ()
  | len == 2  = O.sort2ByOffset cmp vec 0
  | len == 3  = O.sort3ByOffset cmp vec 0
  | len == 4  = O.sort4ByOffset cmp vec 0
  | otherwise = do buf <- new len
                   mergeSortWithBuf cmp vec buf
 where
 len = length vec
{-# INLINE sortBy #-}

mergeSortWithBuf :: (PrimMonad m, MVector v e)
                 => Comparison e -> v (PrimState m) e -> v (PrimState m) e -> m ()
mergeSortWithBuf cmp src buf = loop 0 (length src)
 where
 loop l u
   | len < threshold = I.sortByBounds cmp src l u
   | otherwise       = do loop l mid
                          loop mid u
                          merge cmp (unsafeSlice l len src) buf (mid - l)
  where len = u - l
        mid = (u + l) `shiftR` 1
{-# INLINE mergeSortWithBuf #-}

merge :: (PrimMonad m, MVector v e)
      => Comparison e -> v (PrimState m) e -> v (PrimState m) e
      -> Int -> m ()
merge cmp src buf mid = do unsafeCopy tmp lower
                           eTmp <- unsafeRead tmp 0
                           eUpp <- unsafeRead upper 0
                           loop tmp 0 eTmp upper 0 eUpp 0
 where
 lower = unsafeSlice 0   mid                src
 upper = unsafeSlice mid (length src - mid) src
 tmp   = unsafeSlice 0   mid                buf

 wroteHigh low iLow eLow high iHigh iIns
   | iHigh >= length high = unsafeCopy (unsafeSlice iIns (length low - iLow) src)
                                       (unsafeSlice iLow (length low - iLow) low)
   | otherwise            = do eHigh <- unsafeRead high iHigh
                               loop low iLow eLow high iHigh eHigh iIns

 wroteLow low iLow high iHigh eHigh iIns
   | iLow  >= length low  = return ()
   | otherwise            = do eLow <- unsafeRead low iLow
                               loop low iLow eLow high iHigh eHigh iIns

 loop !low !iLow !eLow !high !iHigh !eHigh !iIns = case cmp eHigh eLow of
     LT -> do unsafeWrite src iIns eHigh
              wroteHigh low iLow eLow high (iHigh + 1) (iIns + 1)
     _  -> do unsafeWrite src iIns eLow
              wroteLow low (iLow + 1) high iHigh eHigh (iIns + 1)
{-# INLINE merge #-}

threshold :: Int
threshold = 25
{-# INLINE threshold #-}
