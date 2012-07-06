#if __GLASGOW_HASKELL__ >= 701 && defined(VECTOR_BOUNDS_CHECKS)
{-# LANGUAGE Trustworthy #-}
#endif

-- |
-- Module      : Data.Vector.Primitive.Safe
-- Copyright   : (c) Roman Leshchinskiy 2008-2010
-- License     : BSD-style
--
-- Maintainer  : Roman Leshchinskiy <rl@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable
--
-- Safe interface to "Data.Vector.Primitive" 
--

module Data.Vector.Primitive.Safe (
  -- * Primitive vectors
  Vector, MVector, Prim,

  -- * Accessors

  -- ** Length information
  length, null,

  -- ** Indexing
  (!), (!?), head, last,

  -- ** Monadic indexing
  indexM, headM, lastM,

  -- ** Extracting subvectors (slicing)
  slice, init, tail, take, drop, splitAt,

  -- * Construction

  -- ** Initialisation
  empty, singleton, replicate, generate, iterateN,

  -- ** Monadic initialisation
  replicateM, generateM, create,

  -- ** Unfolding
  unfoldr, unfoldrN,
  constructN, constructrN,

  -- ** Enumeration
  enumFromN, enumFromStepN, enumFromTo, enumFromThenTo,

  -- ** Concatenation
  cons, snoc, (++), concat,

  -- ** Restricting memory usage
  force,

  -- * Modifying vectors

  -- ** Bulk updates
  (//), update_,

  -- ** Accumulations
  accum, accumulate_,

  -- ** Permutations 
  reverse, backpermute,

  -- ** Safe destructive updates
  modify,

  -- * Elementwise operations

  -- ** Mapping
  map, imap, concatMap,

  -- ** Monadic mapping
  mapM, mapM_, forM, forM_,

  -- ** Zipping
  zipWith, zipWith3, zipWith4, zipWith5, zipWith6,
  izipWith, izipWith3, izipWith4, izipWith5, izipWith6,

  -- ** Monadic zipping
  zipWithM, zipWithM_,

  -- * Working with predicates

  -- ** Filtering
  filter, ifilter, filterM,
  takeWhile, dropWhile,

  -- ** Partitioning
  partition, unstablePartition, span, break,

  -- ** Searching
  elem, notElem, find, findIndex, findIndices, elemIndex, elemIndices,

  -- * Folding
  foldl, foldl1, foldl', foldl1', foldr, foldr1, foldr', foldr1',
  ifoldl, ifoldl', ifoldr, ifoldr',

  -- ** Specialised folds
  all, any,
  sum, product,
  maximum, maximumBy, minimum, minimumBy,
  minIndex, minIndexBy, maxIndex, maxIndexBy,

  -- ** Monadic folds
  foldM, foldM', fold1M, fold1M',
  foldM_, foldM'_, fold1M_, fold1M'_,

  -- * Prefix sums (scans)
  prescanl, prescanl',
  postscanl, postscanl',
  scanl, scanl', scanl1, scanl1',
  prescanr, prescanr',
  postscanr, postscanr',
  scanr, scanr', scanr1, scanr1',

  -- * Conversions

  -- ** Lists
  toList, fromList, fromListN,

  -- ** Other vector types
  G.convert,

  -- ** Mutable vectors
  freeze, thaw, copy,
) where

import Data.Vector.Primitive
import qualified Data.Vector.Generic as G
import Prelude ()

