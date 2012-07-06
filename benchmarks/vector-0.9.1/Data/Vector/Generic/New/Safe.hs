#if __GLASGOW_HASKELL__ >= 701 && defined(VECTOR_BOUNDS_CHECKS)
{-# LANGUAGE Trustworthy #-}
#endif

-- |
-- Module      : Data.Vector.Generic.New.Safe
-- Copyright   : (c) Roman Leshchinskiy 2008-2010
-- License     : BSD-style
--
-- Maintainer  : Roman Leshchinskiy <rl@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable
-- 
-- Safe interface to "Data.Vector.Generic.New"
--

module Data.Vector.Generic.New.Safe (
  New(..), create, run, apply, modify, modifyWithStream,
  unstream, transform, unstreamR, transformR,
  slice, init, tail, take, drop
) where

import Data.Vector.Generic.New
import Prelude ()

