{-# LANGUAGE CPP, DeriveDataTypeable #-}

-- |
-- Module      : Data.Text.Util
-- Copyright   : 2010 Bryan O'Sullivan
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com
-- Stability   : experimental
-- Portability : GHC
--
-- Useful functions.

module Data.Text.Util
    (
      intersperse
    ) where

-- | A lazier version of Data.List.intersperse.  The other version
-- causes space leaks!
intersperse :: a -> [a] -> [a]
intersperse _   []     = []
intersperse sep (x:xs) = x : go xs
  where
    go []     = []
    go (y:ys) = sep : y: go ys
{-# INLINE intersperse #-}
