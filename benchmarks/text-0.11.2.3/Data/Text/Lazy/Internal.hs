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


--LIQUID
import qualified Data.Text.Array
import qualified Data.Text.Fusion.Internal
import qualified Data.Text.Internal
import Language.Haskell.Liquid.Prelude


data Text = Empty
          | Chunk {-# UNPACK #-} !T.Text Text
--LIQUID            deriving (Typeable)

{-@ type NonEmptyStrict = {v:Data.Text.Internal.Text | (tlength v) > 0} @-}

{-@ data Data.Text.Lazy.Internal.Text
      = Empty
      | Chunk (t :: NonEmptyStrict) (cs :: Data.Text.Lazy.Internal.Text)
  @-}

{-@ measure ltlength :: Data.Text.Lazy.Internal.Text -> Integer
    ltlength (Empty)      = 0
    ltlength (Chunk t ts) = (tlength t) + (ltlength ts)
  @-}

-- $invariant
--
-- The data type invariant for lazy 'Text': Every 'Text' is either 'Empty' or
-- consists of non-null 'T.Text's.  All functions must preserve this,
-- and the QC properties must check this.

-- | Check the invariant strictly.
{-@ strictInvariant :: Text -> Bool @-}
strictInvariant :: Text -> Bool
strictInvariant Empty = True
strictInvariant x@(Chunk (T.Text _ _ len) cs)
    | len > 0   = strictInvariant cs
    | otherwise = liquidError $ "Data.Text.Lazy: invariant violation: "
                  ++ showStructure x

-- | Check the invariant lazily.
{-@ lazyInvariant :: Text -> Text @-}
lazyInvariant :: Text -> Text
lazyInvariant Empty = Empty
lazyInvariant x@(Chunk c@(T.Text _ _ len) cs)
    | len > 0   = Chunk c (lazyInvariant cs)
    | otherwise = liquidError $ "Data.Text.Lazy: invariant violation: "
                  ++ showStructure x

-- | Display the internal structure of a lazy 'Text'.
{-@ showStructure :: Text -> String @-}
showStructure :: Text -> String
showStructure Empty           = "Empty"
showStructure (Chunk t Empty) = "Chunk " ++ show t ++ " Empty"
showStructure (Chunk t ts)    =
    "Chunk " ++ show t ++ " (" ++ showStructure ts ++ ")"

-- | Smart constructor for 'Chunk'. Guarantees the data type invariant.
{-@ chunk :: t:Data.Text.Internal.Text
          -> ts:Data.Text.Lazy.Internal.Text
          -> {v:Data.Text.Lazy.Internal.Text | ((ltlength v) = ((tlength t) + (ltlength ts)))} @-}
chunk :: T.Text -> Text -> Text
{-# INLINE chunk #-}
chunk t@(T.Text _ _ len) ts | len == 0 = ts
                            | otherwise = Chunk t ts

-- | Smart constructor for 'Empty'.
{-@ empty :: {v:Data.Text.Lazy.Internal.Text | (ltlength v) = 0} @-}
empty :: Text
{-# INLINE [0] empty #-}
empty = Empty

-- | Consume the chunks of a lazy 'Text' with a natural right fold.
{-@ foldrChunks :: forall <p :: Data.Text.Lazy.Internal.Text -> a -> Prop>.
                   (ts:Data.Text.Lazy.Internal.Text
                    -> t:NonEmptyStrict
                    -> a<p ts>
                    -> a<p (Data.Text.Lazy.Internal.Chunk t ts)>)
                -> a<p Data.Text.Lazy.Internal.Empty>
                -> t:Data.Text.Lazy.Internal.Text
                -> a<p t>
  @-}
foldrChunks :: (Text -> T.Text -> a -> a) -> a -> Text -> a
foldrChunks f z = go
  where go Empty        = z
        go (Chunk c cs) = f cs c (go cs)
--LIQUID foldrChunks :: (T.Text -> a -> a) -> a -> Text -> a
--LIQUID foldrChunks f z = go
--LIQUID   where go Empty        = z
--LIQUID         go (Chunk c cs) = f c (go cs)
{-# INLINE foldrChunks #-}

-- | Consume the chunks of a lazy 'Text' with a strict, tail-recursive,
-- accumulating left fold.
{-@ foldlChunks :: forall <p :: Data.Text.Lazy.Internal.Text -> a -> Prop>.
                   cs:Data.Text.Lazy.Internal.Text
                -> (   a<p cs>
                    -> c:Data.Text.Internal.Text
                    -> a<p cs>)
                -> a<p cs>
                -> t:Data.Text.Lazy.Internal.Text
                -> a<p cs>
  @-}
foldlChunks :: Text -> (a -> T.Text -> a) -> a -> Text -> a
foldlChunks t f !a Empty        = a
foldlChunks t f !a (Chunk c cs) = foldlChunks t f (f a c) cs

--LIQUID foldlChunks :: (a -> T.Text -> a) -> a -> Text -> a
--LIQUID foldlChunks f z = go z
--LIQUID   where go !a Empty        = a
--LIQUID         go !a (Chunk c cs) = go (f a c) cs
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
{-@ chunkOverhead :: Int @-}
chunkOverhead :: Int
chunkOverhead = sizeOf (undefined :: Int) `shiftL` 1
{-# INLINE chunkOverhead #-}
