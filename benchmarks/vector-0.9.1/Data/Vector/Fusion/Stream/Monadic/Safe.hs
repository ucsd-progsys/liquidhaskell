#if __GLASGOW_HASKELL__ >= 701
{-# LANGUAGE Trustworthy #-}
#endif

-- |
-- Module      : Data.Vector.Fusion.Stream.Monadic.Safe
-- Copyright   : (c) Roman Leshchinskiy 2008-2010
-- License     : BSD-style
--
-- Maintainer  : Roman Leshchinskiy <rl@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable
--
-- Safe interface to "Data.Vector.Fusion.Stream.Monadic"
--

module Data.Vector.Fusion.Stream.Monadic.Safe (
  Stream(..), Step(..),

  -- * Size hints
  size, sized,

  -- * Length
  length, null,

  -- * Construction
  empty, singleton, cons, snoc, replicate, replicateM, generate, generateM, (++),

  -- * Accessing elements
  head, last, (!!),

  -- * Substreams
  slice, init, tail, take, drop,

  -- * Mapping
  map, mapM, mapM_, trans, unbox, concatMap, flatten,
  
  -- * Zipping
  indexed, indexedR, zipWithM_,
  zipWithM, zipWith3M, zipWith4M, zipWith5M, zipWith6M,
  zipWith, zipWith3, zipWith4, zipWith5, zipWith6,
  zip, zip3, zip4, zip5, zip6,

  -- * Filtering
  filter, filterM, takeWhile, takeWhileM, dropWhile, dropWhileM,

  -- * Searching
  elem, notElem, find, findM, findIndex, findIndexM,

  -- * Folding
  foldl, foldlM, foldl1, foldl1M, foldM, fold1M,
  foldl', foldlM', foldl1', foldl1M', foldM', fold1M',
  foldr, foldrM, foldr1, foldr1M,

  -- * Specialised folds
  and, or, concatMapM,

  -- * Unfolding
  unfoldr, unfoldrM,
  unfoldrN, unfoldrNM,
  iterateN, iterateNM,

  -- * Scans
  prescanl, prescanlM, prescanl', prescanlM',
  postscanl, postscanlM, postscanl', postscanlM',
  scanl, scanlM, scanl', scanlM',
  scanl1, scanl1M, scanl1', scanl1M',

  -- * Enumerations
  enumFromStepN, enumFromTo, enumFromThenTo,

  -- * Conversions
  toList, fromList, fromListN
) where

import Data.Vector.Fusion.Stream.Monadic
import Prelude ()

