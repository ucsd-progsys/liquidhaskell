{-# LANGUAGE BangPatterns, DeriveDataTypeable #-}
-- |
-- Module      : Data.Text.Lazy.Internal
-- Copyright   : (c) 2009, 2010 Bryan O'Sullivan
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : GHC
--
-- A module containing private 'Text' internals. This exposes the
-- 'Text' representation and low level construction functions.
-- Modules which extend the 'Text' system may need to use this module.
--
-- You should not use this module unless you are determined to monkey
-- with the internals, as the functions here do just about nothing to
-- preserve data invariants.  You have been warned!

module Data.Text.Lazy.Internal
    (
      Text(..)
    , chunk
    , empty
    , foldrChunks
    , foldlChunks
    -- * Data type invariant and abstraction functions

    -- $invariant
    , strictInvariant
    , lazyInvariant
    , showStructure

    -- * Chunk allocation sizes
    , defaultChunkSize
    , smallChunkSize
    , chunkOverhead
    ) where

import Data.Text ()
import Data.Text.UnsafeShift (shiftL)
import Data.Typeable (Typeable)
import Foreign.Storable (sizeOf)
import qualified Data.Text.Internal as T

data Text = Empty
          | Chunk {-# UNPACK #-} !T.Text Text
            deriving (Typeable)

-- $invariant
--
-- The data type invariant for lazy 'Text': Every 'Text' is either 'Empty' or
-- consists of non-null 'T.Text's.  All functions must preserve this,
-- and the QC properties must check this.

-- | Check the invariant strictly.
strictInvariant :: Text -> Bool
strictInvariant Empty = True
strictInvariant x@(Chunk (T.Text _ _ len) cs)
    | len > 0   = strictInvariant cs
    | otherwise = error $ "Data.Text.Lazy: invariant violation: "
                  ++ showStructure x

-- | Check the invariant lazily.
lazyInvariant :: Text -> Text
lazyInvariant Empty = Empty
lazyInvariant x@(Chunk c@(T.Text _ _ len) cs)
    | len > 0   = Chunk c (lazyInvariant cs)
    | otherwise = error $ "Data.Text.Lazy: invariant violation: "
                  ++ showStructure x

-- | Display the internal structure of a lazy 'Text'.
showStructure :: Text -> String
showStructure Empty           = "Empty"
showStructure (Chunk t Empty) = "Chunk " ++ show t ++ " Empty"
showStructure (Chunk t ts)    =
    "Chunk " ++ show t ++ " (" ++ showStructure ts ++ ")"

-- | Smart constructor for 'Chunk'. Guarantees the data type invariant.
chunk :: T.Text -> Text -> Text
{-# INLINE chunk #-}
chunk t@(T.Text _ _ len) ts | len == 0 = ts
                            | otherwise = Chunk t ts

-- | Smart constructor for 'Empty'.
empty :: Text
{-# INLINE [0] empty #-}
empty = Empty

-- | Consume the chunks of a lazy 'Text' with a natural right fold.
foldrChunks :: (T.Text -> a -> a) -> a -> Text -> a
foldrChunks f z = go
  where go Empty        = z
        go (Chunk c cs) = f c (go cs)
{-# INLINE foldrChunks #-}

-- | Consume the chunks of a lazy 'Text' with a strict, tail-recursive,
-- accumulating left fold.
foldlChunks :: (a -> T.Text -> a) -> a -> Text -> a
foldlChunks f z = go z
  where go !a Empty        = a
        go !a (Chunk c cs) = go (f a c) cs
{-# INLINE foldlChunks #-}

-- | Currently set to 16 KiB, less the memory management overhead.
defaultChunkSize :: Int
defaultChunkSize = 16384 - chunkOverhead
{-# INLINE defaultChunkSize #-}

-- | Currently set to 128 bytes, less the memory management overhead.
smallChunkSize :: Int
smallChunkSize = 128 - chunkOverhead
{-# INLINE smallChunkSize #-}

-- | The memory management overhead. Currently this is tuned for GHC only.
chunkOverhead :: Int
chunkOverhead = sizeOf (undefined :: Int) `shiftL` 1
{-# INLINE chunkOverhead #-}
