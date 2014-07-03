{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
import Data.Vector.Algorithms.Common (Comparison, copyOffset, shiftRI)

import qualified Data.Vector.Algorithms.Optimal   as O
import qualified Data.Vector.Algorithms.Insertion as I

{-@ qualif Plus(v:Int, x:Int, y:Int): v = x + y   @-}

-- | Sorts an array using the default comparison.
sort :: (PrimMonad m, MVector v e, Ord e) => v (PrimState m) e -> m ()
sort = sortBy     compare
{-# INLINABLE sort #-}

-- | Sorts an array using a custom comparison.
sortBy :: (PrimMonad m, MVector v e) => Comparison e -> v (PrimState m) e -> m ()
sortBy cmp vec
  | len <= 1  = return ()
  | len == 2  = O.sort2ByOffset cmp vec 0
  | len == 3  = O.sort3ByOffset cmp vec 0
  | len == 4  = O.sort4ByOffset cmp vec 0
  | otherwise = do buf <- new len
                   mergeSortWithBuf  cmp vec buf
 where
 len = length vec
{-# INLINE sortBy #-}

mergeSortWithBuf :: (PrimMonad m, MVector v e)
                 => Comparison e -> v (PrimState m) e -> v (PrimState m) e -> m ()
mergeSortWithBuf cmp src  buf = loop cmp src buf (length src) 0 (length src)
 where
  {- LIQUID WITNESS -}
loop :: (PrimMonad m, MVector v e) 
     => Comparison e
     -> v (PrimState m) e
     -> v (PrimState m) e
     -> Int 
     -> Int 
     -> Int
     -> m ()
loop cmp src buf (twit :: Int) l u
  | len < threshold = I.sortByBounds cmp src l u
  | otherwise       = do loop cmp src buf (mid - l) l mid
                         loop cmp src buf (u - mid) mid u
                         merge cmp (unsafeSlice l len src) buf (mid - l)
 where len = u - l
       mid = (u + l) `shiftRI` 1
{-# INLINE mergeSortWithBuf #-}
{-
merge :: (PrimMonad m, MVector v e)
      => Comparison e 
      -> src:(v (PrimState m) e)
      -> buf:{v:(v (PrimState m) e)| ((vsize v) > 0)}
      -> {v:Int|(((vsize buf) > v) && (v > 0) && ((vsize src) > v))}-> m ()
  @-}
merge :: (PrimMonad m, MVector v e)
      => Comparison e -> v (PrimState m) e -> v (PrimState m) e
      -> Int -> m ()
merge cmp src buf mid = do unsafeCopy low lower
                           eLow  <- unsafeRead low  0
                           eHigh <- unsafeRead high 0
                           loopMerge (length low + length high) 0 0 eLow 0 eHigh 0
 where
 lower = unsafeSlice 0   mid src
 high  = unsafeSlice mid nHi src -- upper
 low   = unsafeSlice 0   mid buf -- tmp
 nHi   = nSrc - mid
 nSrc  = length src -- liquidAssume (length src > mid) src)
--  nSrc  = length (liquidAssume (length src > mid) src)


{-@ Decrease wroteHigh 1 2 @-}
{-@ Decrease wroteLow 1 2 @-}
{-@ Decrease loopMerge 1 2 @-}

  {- LIQUID WITNESS -}
 wroteHigh d1 (d2::Int) iLow eLow iHigh iIns
   | iHigh >= length high = unsafeCopy (unsafeSlice iIns (length low - iLow) src)
                                       (unsafeSlice iLow (length low - iLow) low)
   | otherwise            = do eHigh <- unsafeRead high iHigh
                               loopMerge d1 0 iLow eLow iHigh eHigh iIns

  {- LIQUID WITNESS -}
 wroteLow d1 (d2::Int) iLow iHigh eHigh iIns
   | iLow  >= length low  = return ()
   | otherwise            = do eLow <- unsafeRead low iLow
                               loopMerge d1 0 iLow eLow iHigh eHigh iIns

  {- LIQUID WITNESS -}
 loopMerge (d::Int) (d2::Int) !iLow !eLow !iHigh !eHigh !iIns = case cmp eHigh eLow of
     LT -> do unsafeWrite src iIns eHigh
              wroteHigh (d-1) 1 iLow eLow (iHigh + 1) (iIns + 1)
     _  -> do unsafeWrite src iIns eLow
              wroteLow (d-1) 1 (iLow + 1) iHigh eHigh (iIns + 1)
{-# INLINE merge #-}

threshold :: Int
threshold = 25
{-# INLINE threshold #-}


liquidAssume :: Bool -> a -> a
{-@ liquidAssume :: p:Bool -> a -> {v:a | (Prop p)} @-}
liquidAssume = undefined

quals :: (PrimMonad m, MVector v e) => v (PrimState m) e -> Int -> Bool -> m () 
{-@ quals :: (PrimMonad m, MVector v e) 
          => src:(v (PrimState m) e) 
          -> n:{v:Int| (vsize src) > v} 
          -> {v:Bool | (vsize src) > n}
          -> m () @-}
quals = undefined






















