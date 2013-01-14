{-# LANGUAGE CPP, ForeignFunctionInterface #-}
-- We cannot actually specify all the language pragmas, see ghc ticket #
-- If we could, these are what they would be:
{- LANGUAGE DeriveDataTypeable -}
{-# OPTIONS_HADDOCK hide #-}

-- |
-- Module      : Data.ByteString.Lazy.Internal
-- License     : BSD-style
-- Maintainer  : dons@galois.com, duncan@haskell.org
-- Stability   : experimental
-- Portability : portable
-- 
-- A module containing semi-public 'ByteString' internals. This exposes
-- the 'ByteString' representation and low level construction functions.
-- Modules which extend the 'ByteString' system will need to use this module
-- while ideally most users will be able to make do with the public interface
-- modules.
--
module Data.ByteString.Lazy.Internal (

        -- * The lazy @ByteString@ type and representation
        ByteString(..),     -- instances: Eq, Ord, Show, Read, Data, Typeable
        chunk,
        foldrChunks,
        foldlChunks,

        -- * Data type invariant and abstraction function
        invariant,
        checkInvariant,

        -- * Chunk allocation sizes
        defaultChunkSize,
        smallChunkSize,
        chunkOverhead

  ) where

import qualified Data.ByteString.Internal as S

import Foreign.Storable (Storable(sizeOf))

#if defined(__GLASGOW_HASKELL__)
import Data.Typeable    (Typeable)
#if __GLASGOW_HASKELL__ >= 610
import Data.Data        (Data)
#else
import Data.Generics    (Data)
#endif
#endif

-- | A space-efficient representation of a Word8 vector, supporting many
-- efficient operations.  A 'ByteString' contains 8-bit characters only.
--
-- Instances of Eq, Ord, Read, Show, Data, Typeable
--
data ByteString = Empty | Chunk {-# UNPACK #-} !S.ByteString ByteString
    deriving (Show, Read
#if defined(__GLASGOW_HASKELL__)
                        ,Data, Typeable
#endif
             )

------------------------------------------------------------------------

-- | The data type invariant:
-- Every ByteString is either 'Empty' or consists of non-null 'S.ByteString's.
-- All functions must preserve this, and the QC properties must check this.
--
invariant :: ByteString -> Bool
invariant Empty                     = True
invariant (Chunk (S.PS _ _ len) cs) = len > 0 && invariant cs

-- | In a form that checks the invariant lazily.
checkInvariant :: ByteString -> ByteString
checkInvariant Empty = Empty
checkInvariant (Chunk c@(S.PS _ _ len) cs)
    | len > 0   = Chunk c (checkInvariant cs)
    | otherwise = error $ "Data.ByteString.Lazy: invariant violation:"
               ++ show (Chunk c cs)

------------------------------------------------------------------------

-- | Smart constructor for 'Chunk'. Guarantees the data type invariant.
chunk :: S.ByteString -> ByteString -> ByteString
chunk c@(S.PS _ _ len) cs | len == 0  = cs
                          | otherwise = Chunk c cs
{-# INLINE chunk #-}

-- | Consume the chunks of a lazy ByteString with a natural right fold.
foldrChunks :: (S.ByteString -> a -> a) -> a -> ByteString -> a
foldrChunks f z = go
  where go Empty        = z
        go (Chunk c cs) = f c (go cs)
{-# INLINE foldrChunks #-}

-- | Consume the chunks of a lazy ByteString with a strict, tail-recursive,
-- accumulating left fold.
foldlChunks :: (a -> S.ByteString -> a) -> a -> ByteString -> a
foldlChunks f z = go z
  where go a _ | a `seq` False = undefined
        go a Empty        = a
        go a (Chunk c cs) = go (f a c) cs
{-# INLINE foldlChunks #-}

------------------------------------------------------------------------

-- The representation uses lists of packed chunks. When we have to convert from
-- a lazy list to the chunked representation, then by default we use this
-- chunk size. Some functions give you more control over the chunk size.
--
-- Measurements here:
--  http://www.cse.unsw.edu.au/~dons/tmp/chunksize_v_cache.png
--
-- indicate that a value around 0.5 to 1 x your L2 cache is best.
-- The following value assumes people have something greater than 128k,
-- and need to share the cache with other programs.

-- | Currently set to 32k, less the memory management overhead
defaultChunkSize :: Int
defaultChunkSize = 32 * k - chunkOverhead
   where k = 1024

-- | Currently set to 4k, less the memory management overhead
smallChunkSize :: Int
smallChunkSize = 4 * k - chunkOverhead
   where k = 1024

-- | The memory management overhead. Currently this is tuned for GHC only.
chunkOverhead :: Int
chunkOverhead = 2 * sizeOf (undefined :: Int)
