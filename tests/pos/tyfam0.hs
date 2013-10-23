{-# LANGUAGE FlexibleContexts #-}

-- ---------------------------------------------------------------------------
-- |
-- Module      : Data.Vector.Algorithms.Common
-- Copyright   : (c) 2008-2011 Dan Doel
-- Maintainer  : Dan Doel
-- Stability   : Experimental
-- Portability : Portable
--
-- Common operations and utility functions for all sorts

module Data.Vector.Algorithms.Common where

import Prelude hiding (read, length)

import Control.Monad.Primitive

-- copyOffset :: (PrimMonad m, MVector v e) => v (PrimState m) e -> a 
copyOffset :: (PrimMonad m) => (PrimState m) -> a 
copyOffset = undefined

