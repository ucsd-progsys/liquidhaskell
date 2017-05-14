{-@ LIQUID "--maxparams=3" @-}
{-@ LIQUID "--prune-unsorted" @-}

{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
-- |
-- Module      : Data.ByteString.Lazy.Internal
-- License     : BSD-style
-- Maintainer  : dons@cse.unsw.edu.au, duncan@haskell.org
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

        liquidCanary, 

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

-- LIQUID
import Language.Haskell.Liquid.Prelude  (liquidError)
-- import qualified Data.ByteString.Internal
-- import Foreign.ForeignPtr       (ForeignPtr)
-- import Data.Word                (Word, Word8, Word16, Word32, Word64)
-- import Foreign.Ptr              (Ptr)
-- import qualified Foreign.C.String

import Foreign.Storable (sizeOf)

#if defined(__GLASGOW_HASKELL__)
import Data.Generics            (Data(..), Typeable(..))
#endif

-- | A space-efficient representation of a Word8 vector, supporting many
-- efficient operations.  A 'ByteString' contains 8-bit characters only.
--
-- Instances of Eq, Ord, Read, Show, Data, Typeable
--
data ByteString = Empty | Chunk {-# UNPACK #-} !S.ByteString ByteString
    deriving (Show)
-- LIQUID     deriving (Show, Read
-- LIQUID #if defined(__GLASGOW_HASKELL__)
-- LIQUID                         ,Data, Typeable
-- LIQUID #endif
-- LIQUID              )

{-@ data ByteString [lbLength]
         = Empty
         | Chunk (b :: ByteStringNE) (cs :: ByteString)
  @-}

{-@ measure lbLength :: ByteString -> Int
    lbLength (Empty)      = 0
    lbLength (Chunk b bs) = (bLength b) + (lbLength bs)
  @-}

{-@ measure lbLengths  :: [ByteString] -> Int
    lbLengths ([])   = 0
    lbLengths (x:xs) = (lbLength x) + (lbLengths xs)
  @-}

{-@ invariant {v:ByteString   | (lbLength v)  >= 0} @-}
{-@ invariant {v:[ByteString] | (lbLengths v) >= 0} @-}

{-@ type LByteStringSplit B = {v:[ByteString] | ((lbLengths v) + (len v) - 1) = (lbLength B) }
  @-}

{-@ type LByteStringPair B = (ByteString, ByteString)<{\x1 x2 -> (lbLength x1) + (lbLength x2) = (lbLength B)}>
  @-}

{-@ predicate LBValid B N = ((N >= 0) && (N < (lbLength B))) @-}

{-@ type LByteStringN N  = {v:ByteString | (lbLength v) = N} @-}
{-@ type LByteStringNE   = {v:ByteString | (lbLength v) > 0} @-}
{-@ type LByteStringSZ B = {v:ByteString | (lbLength v) = (lbLength B)} @-}
{-@ type LByteStringLE B = {v:ByteString | (lbLength v) <= (lbLength B)} @-}

------------------------------------------------------------------------

{- liquidCanary :: x:Int -> {v: Int | v > x} @-}
liquidCanary     :: Int -> Int
liquidCanary x   = x - 1


-- | The data type invariant:
-- Every ByteString is either 'Empty' or consists of non-null 'S.ByteString's.
-- All functions must preserve this, and the QC properties must check this.
--

-- LIQUID RENAME: rename `invariant` to `invt` to avoid name clash!
{-@ invt :: ByteString -> {v: Bool | (Prop v)}  @-}
invt :: ByteString -> Bool
invt Empty                     = True 
invt (Chunk (S.PS _ _ len) cs) = len > 0 && invt cs

invariant = invt

-- | In a form that checks the invariant lazily.
{-@ checkInvariant :: ByteString -> ByteString  @-}
checkInvariant :: ByteString -> ByteString
checkInvariant Empty = Empty
checkInvariant (Chunk c@(S.PS _ _ len) cs)
    | len > 0   = Chunk c (checkInvariant cs)
    | otherwise = liquidError $ "Data.ByteString.Lazy: invariant violation:"
               ++ show (Chunk c cs)

------------------------------------------------------------------------

-- | Smart constructor for 'Chunk'. Guarantees the data type invariant.
{-@ chunk :: b:S.ByteString -> bs:ByteString
          -> {v:ByteString | (lbLength v) = ((bLength b) + (lbLength bs))}
  @-}
chunk :: S.ByteString -> ByteString -> ByteString
chunk c@(S.PS _ _ len) cs | len == 0  = cs
                          | otherwise = Chunk c cs
{-# INLINE chunk #-}

-- | Consume the chunks of a lazy ByteString with a natural right fold.
{-@ foldrChunks :: forall <p :: ByteString -> a -> Prop>.
                   (bs:ByteString
                    -> b:ByteStringNE
                    -> a<p bs>
                    -> a<p (Chunk b bs)>)
                -> a<p Empty>
                -> b:ByteString
                -> a<p b>
  @-}
--LIQUID GHOST added parameter to `f` for abstract refinement
foldrChunks :: (ByteString -> S.ByteString -> a -> a) -> a -> ByteString -> a
foldrChunks f z = go
  where go Empty        = z
        go (Chunk c cs) = f cs c (go cs)
{-# INLINE foldrChunks #-}

-- | Consume the chunks of a lazy ByteString with a strict, tail-recursive,
-- accumulating left fold.
{-@ foldlChunks :: (a -> ByteStringNE -> a)
                -> a
                -> ByteString
                -> a
  @-}
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
{-@ defaultChunkSize :: {v:Nat | v = 32752} @-}
defaultChunkSize :: Int
defaultChunkSize = {-LIUQID MULTIPLY 32 * k -} 32768 - chunkOverhead
   where k = 1024

-- | Currently set to 4k, less the memory management overhead
{-@ smallChunkSize :: {v:Nat | v = 4080} @-}
smallChunkSize :: Int
smallChunkSize = {-LIQUID MULTIPLY 4 * k -} 4096 - chunkOverhead
   where k = 1024

-- | The memory management overhead. Currently this is tuned for GHC only.
{-@ chunkOverhead :: {v:Nat | v = 16} @-}
chunkOverhead :: Int
chunkOverhead = 2 * sizeOf (undefined :: Int)
