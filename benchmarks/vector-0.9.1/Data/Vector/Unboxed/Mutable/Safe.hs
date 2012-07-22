#if __GLASGOW_HASKELL__ >= 701 && defined(VECTOR_BOUNDS_CHECKS)
{-# LANGUAGE Trustworthy #-}
#endif
-- |
-- Module      : Data.Vector.Unboxed.Mutable.Safe
-- Copyright   : (c) Roman Leshchinskiy 2009-2010
-- License     : BSD-style
--
-- Maintainer  : Roman Leshchinskiy <rl@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable
--
-- Safe interface to "Data.Vector.Unboxed.Mutable"
--

module Data.Vector.Unboxed.Mutable.Safe (
  -- * Mutable vectors of primitive types
  MVector, IOVector, STVector, Unbox,

  -- * Accessors

  -- ** Length information
  length, null,

  -- ** Extracting subvectors
  slice, init, tail, take, drop, splitAt,

  -- ** Overlapping
  overlaps,

  -- * Construction

  -- ** Initialisation
  new, replicate, replicateM, clone,

  -- ** Growing
  grow,

  -- ** Restricting memory usage
  clear,

  -- * Zipping and unzipping
  zip, zip3, zip4, zip5, zip6,
  unzip, unzip3, unzip4, unzip5, unzip6,

  -- * Accessing individual elements
  read, write, swap,

  -- * Modifying vectors

  -- ** Filling and copying
  set, copy, move
) where

import Data.Vector.Unboxed.Mutable
import Prelude ()

