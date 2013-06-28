{--! run liquid with maxparams=3 -}
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
import qualified Data.ByteString.Internal
import Foreign.ForeignPtr       (ForeignPtr)
import Data.Word                (Word, Word8, Word16, Word32, Word64)
import Foreign.Ptr              (Ptr)
import qualified Foreign.C.String

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

{-@ data Data.ByteString.Lazy.Internal.ByteString
         = Data.ByteString.Lazy.Internal.Empty 
         | Data.ByteString.Lazy.Internal.Chunk
                (b  :: ByteStringNE)
                (cs :: Data.ByteString.Lazy.Internal.ByteString)
  @-}

{-@ measure lbLength :: Data.ByteString.Lazy.Internal.ByteString -> Int
    lbLength (Data.ByteString.Lazy.Internal.Empty) = 0
    lbLength (Data.ByteString.Lazy.Internal.Chunk b bs) = (bLength b) + (lbLength bs)
  @-}

{-@ measure lbLengths  :: [Data.ByteString.Lazy.Internal.ByteString] -> Int
    lbLengths ([])   = 0
    lbLengths (x:xs) = (lbLength x) + (lbLengths xs)
  @-}

{-@ qualif LBLensAcc(v:Data.ByteString.Lazy.Internal.ByteString,
                     bs:List Data.ByteString.Lazy.Internal.ByteString,
                     b:Data.ByteString.Lazy.Internal.ByteString):
        lbLength(v) = lbLengths(bs) + lbLength(b)
  @-}

{-@ invariant {v:LByteString   | (lbLength v)  >= 0} @-}
{-@ invariant {v:[LByteString] | (lbLengths v) >= 0} @-}

{-@ type LByteStringSplit B = {v:[LByteString] | ((lbLengths v) + (len v) - 1) = (lbLength B) }
  @-}

{-@ type LByteStringPair B = (LByteString, LByteString)<{\x1 x2 -> (lbLength x1) + (lbLength x2) = (lbLength B)}>
  @-}

{-@ predicate LBValid B N = ((N >= 0) && (N < (lbLength B))) @-}

{-@ type LByteString     = {v:Data.ByteString.Lazy.Internal.ByteString | true} @-}
{-@ type LByteStringN N  = {v:LByteString | (lbLength v) = N} @-}
{-@ type LByteStringNE   = {v:LByteString | (lbLength v) > 0} @-}
{-@ type LByteStringSZ B = {v:LByteString | (lbLength v) = (lbLength B)} @-}
{-@ type LByteStringLE B = {v:LByteString | (lbLength v) <= (lbLength B)} @-}

-- ByteString qualifiers
{-@ qualif ByteStringNE(v:Data.ByteString.Internal.ByteString): (bLength v) > 0 @-}
{-@ qualif BLengthsAcc(v:List Data.ByteString.Internal.ByteString,
                       c:Data.ByteString.Internal.ByteString,
                       cs:List Data.ByteString.Internal.ByteString):
        (bLengths v) = (bLength c) + (bLengths cs)
  @-}

{-@ qualif BLengthsSum(v:List List a, bs:List Data.ByteString.Internal.ByteString):
       (sumLens v) = (bLengths bs)
  @-}

{-@ qualif BLenLE(v:Data.ByteString.Internal.ByteString, n:int): (bLength v) <= n @-}
{-@ qualif BLenEq(v:Data.ByteString.Internal.ByteString,
                  b:Data.ByteString.Internal.ByteString):
       (bLength v) = (bLength b)
  @-}

{-@ qualif BLenAcc(v:int,
                   b1:Data.ByteString.Internal.ByteString,
                   b2:Data.ByteString.Internal.ByteString):
       v = (bLength b1) + (bLength b2)
  @-}
{-@ qualif BLenAcc(v:int,
                   b:Data.ByteString.Internal.ByteString,
                   n:int):
       v = (bLength b) + n
  @-}

-- lazy ByteString qualifiers
{-@ qualif LByteStringN(v:Data.ByteString.Lazy.Internal.ByteString, n:int): (lbLength v) = n @-}
{-@ qualif LByteStringNE(v:Data.ByteString.Lazy.Internal.ByteString): (lbLength v) > 0 @-}
{-@ qualif LByteStringSZ(v:Data.ByteString.Lazy.Internal.ByteString,
                         b:Data.ByteString.Lazy.Internal.ByteString):
        (lbLength v) = (lbLength b)
  @-}

{-@ qualif LBLenAcc(v:int,
                    b1:Data.ByteString.Lazy.Internal.ByteString,
                    b2:Data.ByteString.Lazy.Internal.ByteString):
       v = (lbLength b1) + (lbLength b2)
  @-}

{-@ qualif LBLenAcc(v:int,
                    b:Data.ByteString.Lazy.Internal.ByteString,
                    n:int):
       v = (lbLength b) + n
  @-}

{-@ qualif Chunk(v:Data.ByteString.Lazy.Internal.ByteString,
                 sb:Data.ByteString.Internal.ByteString,
                 lb:Data.ByteString.Lazy.Internal.ByteString):
       (lbLength v) = (bLength sb) + (lbLength lb)
  @-}

--LIQUID for the myriad `comb` inner functions
{-@ qualif LBComb(v:List Data.ByteString.Lazy.Internal.ByteString,
                  acc:List Data.ByteString.Internal.ByteString,
                  ss:List Data.ByteString.Internal.ByteString,
                  cs:Data.ByteString.Lazy.Internal.ByteString):
        ((lbLengths v) + (len v) - 1) = ((bLengths acc) + ((bLengths ss) + (len ss) - 1) + (lbLength cs))
  @-}

{-@ qualif LBGroup(v:List Data.ByteString.Lazy.Internal.ByteString,
                   acc:List Data.ByteString.Internal.ByteString,
                   ss:List Data.ByteString.Internal.ByteString,
                   cs:Data.ByteString.Lazy.Internal.ByteString):
        (lbLengths v) = ((bLengths acc) + (bLengths ss) + (lbLength cs))
  @-}

{-@ qualif LBLenIntersperse(v:Data.ByteString.Lazy.Internal.ByteString,
                            sb:Data.ByteString.Internal.ByteString,
                            lb:Data.ByteString.Lazy.Internal.ByteString):
        (lbLength v) = ((bLength sb) * 2) + (lbLength lb)
 @-}

{-@ qualif BLenDouble(v:Data.ByteString.Internal.ByteString,
                      b:Data.ByteString.Internal.ByteString):
        (bLength v) = (bLength b) * 2
 @-}

{-@ qualif LBLenDouble(v:Data.ByteString.Lazy.Internal.ByteString,
                       b:Data.ByteString.Lazy.Internal.ByteString):
        (lbLength v) = (lbLength b) * 2
 @-}

{-@ qualif RevChunksAcc(v:Data.ByteString.Lazy.Internal.ByteString,
                        acc:Data.ByteString.Lazy.Internal.ByteString,
                        cs:List Data.ByteString.Internal.ByteString):
        (lbLength v) = (lbLength acc) + (bLengths cs)
  @-}

{-@ qualif LBSumLens(v:Data.ByteString.Lazy.Internal.ByteString,
                     z:Data.ByteString.Lazy.Internal.ByteString,
                     cs:List List a):
        (lbLength v) = (lbLength z) + (sumLens cs)
  @-}
{-@ qualif LBCountAcc(v:int,
                     c:Data.ByteString.Internal.ByteString,
                     cs:Data.ByteString.Lazy.Internal.ByteString):
       v <= (bLength c) + (lbLength cs)
  @-}

------------------------------------------------------------------------

{- liquidCanary :: x:Int -> {v: Int | v > x} @-}
liquidCanary     :: Int -> Int
liquidCanary x   = x - 1


-- | The data type invariant:
-- Every ByteString is either 'Empty' or consists of non-null 'S.ByteString's.
-- All functions must preserve this, and the QC properties must check this.
--

-- LIQUID: rename `invariant` to `invt` to avoid name clash! 
{-@ invt :: Data.ByteString.Lazy.Internal.ByteString -> {v: Bool | (Prop v)}  @-}
invt :: ByteString -> Bool
invt Empty                     = True 
invt (Chunk (S.PS _ _ len) cs) = len > 0 && invt cs

invariant = invt

-- | In a form that checks the invariant lazily.
{-@ checkInvariant :: Data.ByteString.Lazy.Internal.ByteString -> Data.ByteString.Lazy.Internal.ByteString  @-}
checkInvariant :: ByteString -> ByteString
checkInvariant Empty = Empty
checkInvariant (Chunk c@(S.PS _ _ len) cs)
    | len > 0   = Chunk c (checkInvariant cs)
    | otherwise = liquidError $ "Data.ByteString.Lazy: invariant violation:"
               ++ show (Chunk c cs)

------------------------------------------------------------------------

-- | Smart constructor for 'Chunk'. Guarantees the data type invariant.
{-@ chunk :: b:ByteString -> bs:LByteString
          -> {v:LByteString | (lbLength v) = ((bLength b) + (lbLength bs))}
  @-}
chunk :: S.ByteString -> ByteString -> ByteString
chunk c@(S.PS _ _ len) cs | len == 0  = cs
                          | otherwise = Chunk c cs
{-# INLINE chunk #-}

-- | Consume the chunks of a lazy ByteString with a natural right fold.
{-@ foldrChunks :: forall <p :: Data.ByteString.Lazy.Internal.ByteString -> a -> Prop>.
                   (bs:LByteString
                    -> b:ByteStringNE
                    -> a<p bs>
                    -> a<p (Data.ByteString.Lazy.Internal.Chunk b bs)>)
                -> a<p Data.ByteString.Lazy.Internal.Empty>
                -> b:LByteString
                -> a<p b>
  @-}
--LIQUID added parameter to `f` for abstract refinement
foldrChunks :: (ByteString -> S.ByteString -> a -> a) -> a -> ByteString -> a
foldrChunks f z = go
  where go Empty        = z
        go (Chunk c cs) = f cs c (go cs)
{-# INLINE foldrChunks #-}

-- | Consume the chunks of a lazy ByteString with a strict, tail-recursive,
-- accumulating left fold.
{-@ foldlChunks :: (a -> ByteStringNE -> a)
                -> a
                -> LByteString
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
defaultChunkSize = {-LIUQID 32 * k -} 32768 - chunkOverhead
   where k = 1024

-- | Currently set to 4k, less the memory management overhead
{-@ smallChunkSize :: {v:Nat | v = 4080} @-}
smallChunkSize :: Int
smallChunkSize = {-LIQUID 4 * k -} 4096 - chunkOverhead
   where k = 1024

-- | The memory management overhead. Currently this is tuned for GHC only.
{-@ chunkOverhead :: {v:Nat | v = 16} @-}
chunkOverhead :: Int
chunkOverhead = 2 * sizeOf (undefined :: Int)
