#if __GLASGOW_HASKELL__ >= 701 && defined(VECTOR_BOUNDS_CHECKS)
{-# LANGUAGE Trustworthy #-}
#endif
-- |
-- Module      : Data.Vector.Primitive.Mutable.Safe
-- Copyright   : (c) Roman Leshchinskiy 2008-2010
-- License     : BSD-style
--
-- Maintainer  : Roman Leshchinskiy <rl@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable
-- 
-- Safe interface to "Data.Vector.Primitive.Mutable"
--

module Data.Vector.Primitive.Mutable.Safe (
  -- * Mutable vectors of primitive types
  MVector, IOVector, STVector, Prim,

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

  -- * Accessing individual elements
  read, write, swap,

  -- * Modifying vectors

  -- ** Filling and copying
  set, copy, move
) where

import Data.Vector.Primitive.Mutable
import Prelude ()

