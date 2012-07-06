#if __GLASGOW_HASKELL__ >= 701
{-# LANGUAGE Trustworthy #-}
#endif

-- |
-- Module      : Data.Vector.Fusion.Stream.Safe
-- Copyright   : (c) Roman Leshchinskiy 2008-2010
-- License     : BSD-style
--
-- Maintainer  : Roman Leshchinskiy <rl@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable
-- 
-- Safe interface to "Data.Vector.Fusion.Stream"
--

module Data.Vector.Fusion.Stream.Safe (
  -- * Types
  Step(..), Stream, MStream,

  -- * In-place markers
  inplace,

  -- * Size hints
  size, sized,

  -- * Length information
  length, null,

  -- * Construction
  empty, singleton, cons, snoc, replicate, generate, (++),

  -- * Accessing individual elements
  head, last, (!!),

  -- * Substreams
  slice, init, tail, take, drop,

  -- * Mapping
  map, concatMap, flatten, unbox,
  
  -- * Zipping
  indexed, indexedR,
  zipWith, zipWith3, zipWith4, zipWith5, zipWith6,
  zip, zip3, zip4, zip5, zip6,

  -- * Filtering
  filter, takeWhile, dropWhile,

  -- * Searching
  elem, notElem, find, findIndex,

  -- * Folding
  foldl, foldl1, foldl', foldl1', foldr, foldr1,

  -- * Specialised folds
  and, or,

  -- * Unfolding
  unfoldr, unfoldrN, iterateN,

  -- * Scans
  prescanl, prescanl',
  postscanl, postscanl',
  scanl, scanl',
  scanl1, scanl1',

  -- * Enumerations
  enumFromStepN, enumFromTo, enumFromThenTo,

  -- * Conversions
  toList, fromList, fromListN, liftStream,

  -- * Monadic combinators
  mapM, mapM_, zipWithM, zipWithM_, filterM, foldM, fold1M, foldM', fold1M',

  eq, cmp
) where

import Data.Vector.Fusion.Stream
import Prelude ()

