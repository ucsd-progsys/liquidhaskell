{-# LANGUAGE BangPatterns, CPP, ForeignFunctionInterface, MagicHash, Rank2Types,
    RecordWildCards, UnboxedTuples, UnliftedFFITypes #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
-- |
-- Module      : Data.Text.Array
-- Copyright   : (c) 2009, 2010, 2011 Bryan O'Sullivan
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : portable
--
-- Packed, unboxed, heap-resident arrays.  Suitable for performance
-- critical use, both in terms of large data quantities and high
-- speed.
--
-- This module is intended to be imported @qualified@, to avoid name
-- clashes with "Prelude" functions, e.g.
--
-- > import qualified Data.Text.Array as A
--
-- The names in this module resemble those in the 'Data.Array' family
-- of modules, but are shorter due to the assumption of qualifid
-- naming.
module Data.Text.Array
    (
    -- * Types
    --LIQUID added Array dataCon export
      Array(..)
--LIQUID     , MArray(maBA)
    , MArray(..)

    -- * Functions
    , copyM
    , copyI
    , empty
    , equal
--LIQUID #if defined(ASSERTS)
    , length
--LIQUID #endif
    , run
    , run2
    , toList
    , unsafeFreeze
    , unsafeIndex
    , new
    , unsafeWrite
    --LIQUID
    , unsafeIndexF
    , unsafeIndexB
    ) where

#if defined(ASSERTS)
-- This fugly hack is brought by GHC's apparent reluctance to deal
-- with MagicHash and UnboxedTuples when inferring types. Eek!
# define CHECK_BOUNDS(_func_,_len_,_k_) \
if (_k_) < 0 || (_k_) >= (_len_) then error ("Data.Text.Array." ++ (_func_) ++ ": bounds error, offset " ++ show (_k_) ++ ", length " ++ show (_len_)) else
#else
# define CHECK_BOUNDS(_func_,_len_,_k_)
#endif

#include "MachDeps.h"

--LIQUID #if defined(ASSERTS)
import Control.Exception (assert)
--LIQUID #endif
#if __GLASGOW_HASKELL__ >= 702
import Control.Monad.ST.Unsafe (unsafeIOToST)
#else
import Control.Monad.ST (unsafeIOToST)
#endif
import Data.Bits ((.&.), xor)
import Data.Text.Unsafe.Base (inlinePerformIO)
import Data.Text.UnsafeShift (shiftL, shiftR)
#if __GLASGOW_HASKELL__ >= 703
import Foreign.C.Types (CInt(CInt), CSize(CSize))
#else
import Foreign.C.Types (CInt, CSize)
#endif
import GHC.Base (ByteArray#, MutableByteArray#, Int(..),
                 indexWord16Array#, newByteArray#,
                 unsafeCoerce#, writeWord16Array#)
import GHC.ST (ST(..), runST)
import GHC.Word (Word16(..))
import Prelude hiding (length, read)

--LIQUID
import Data.Int
import qualified Data.Word
import qualified GHC.Prim
import Language.Haskell.Liquid.Prelude

-- | Immutable array type.
data Array = Array {
      aBA :: ByteArray#
--LIQUID #if defined(ASSERTS)
    , aLen :: {-# UNPACK #-} !Int -- length (in units of Word16, not bytes)
--LIQUID #endif
    }

{-@ data Data.Text.Array.Array <p :: Int -> Prop>
         = Data.Text.Array.Array
            (aBA :: GHC.Prim.ByteArray#)
            (aLen :: Nat<p>)
  @-}

{-@ measure alen :: Data.Text.Array.Array -> Int
    alen (Data.Text.Array.Array aBA aLen) = aLen
  @-}

{-@ aLen :: a:Data.Text.Array.Array
         -> {v:Nat | v = (alen a)}
  @-}

{-@ invariant {v:Data.Text.Array.Array | (alen v) >= 0} @-}

{-@ measure numchars :: Data.Text.Array.Array -> Int -> Int -> Int @-}

-- | Mutable array type, for use in the ST monad.
data MArray s = MArray {
      maBA :: MutableByteArray# s
--LIQUID #if defined(ASSERTS)
    , maLen :: {-# UNPACK #-} !Int -- length (in units of Word16, not bytes)
--LIQUID #endif
    }

{-@ data Data.Text.Array.MArray s <p :: Int -> Prop>
         = Data.Text.Array.MArray
            (maBA :: GHC.Prim.MutableByteArray# s)
            (maLen :: Nat<p>)
  @-}

{-@ measure malen :: Data.Text.Array.MArray s -> Int
    malen (Data.Text.Array.MArray maBA maLen) = maLen
  @-}

{-@ maLen :: ma:(Data.Text.Array.MArray s)
          -> {v:Nat | v = (malen ma)}
  @-}

{-@ invariant {v:Data.Text.Array.MArray | (malen v) >= 0} @-}

--LIQUID #if defined(ASSERTS)
-- | Operations supported by all arrays.
class IArray a where
    -- | Return the length of an array.
    length :: a -> Int

instance IArray Array where
    length = aLen
    {-# INLINE length #-}

instance IArray (MArray s) where
    length = maLen
    {-# INLINE length #-}
--LIQUID #endif

-- | Create an uninitialized mutable array.
{-@ new :: forall s. n:Nat
        -> GHC.ST.ST s ({v:Data.Text.Array.MArray s | (malen v) = n})
  @-}
new :: forall s. Int -> ST s (MArray s)
new n
  | n < 0 || n .&. highBit /= 0 = error $ "Data.Text.Array.new: size overflow"
  | otherwise = ST $ \s1# ->
       case newByteArray# len# s1# of
         (# s2#, marr# #) -> (# s2#, MArray marr#
--LIQUID #if defined(ASSERTS)
                                n
--LIQUID #endif
                                #)
  where !(I# len#) = bytesInArray n
        highBit    = maxBound `xor` (maxBound `shiftR` 1)
{-# INLINE new #-}

-- | Freeze a mutable array. Do not mutate the 'MArray' afterwards!
{-@ unsafeFreeze :: ma:Data.Text.Array.MArray s
                 -> (ST s {v:Data.Text.Array.Array | (alen v) = (malen ma)})
  @-}
unsafeFreeze :: MArray s -> ST s Array
unsafeFreeze MArray{..} = ST $ \s# ->
                          (# s#, Array (unsafeCoerce# maBA)
--LIQUID #if defined(ASSERTS)
                             maLen
--LIQUID #endif
                             #)
{-# INLINE unsafeFreeze #-}

-- | Indicate how many bytes would be used for an array of the given
-- size.
bytesInArray :: Int -> Int
bytesInArray n = n `shiftL` 1
{-# INLINE bytesInArray #-}

-- | Unchecked read of an immutable array.  May return garbage or
-- crash on an out-of-bounds access.
{-@ unsafeIndex :: a:Data.Text.Array.Array
                -> i:{v:Nat | v < (alen a)}
                -> Data.Word.Word16
  @-}
unsafeIndex :: Array -> Int -> Word16
unsafeIndex Array{..} i@(I# i#) =
  CHECK_BOUNDS("unsafeIndex",aLen,i)
    case indexWord16Array# aBA i# of r# -> (W16# r#)
{-# INLINE unsafeIndex #-}

--LIQUID
{-@ unsafeIndexF :: a:Data.Text.Array.Array
                 -> o:{v:Int | (BtwnI v 0 (alen a))}
                 -> l:{v:Int | ((v >= 0) && ((o+v) <= (alen a)))}
                 -> i:{v:Int | (Btwn (v) (o) (o + l))}
                 -> {v:Data.Word.Word16 | (((v >= 55296) && (v <= 56319))
                                           ? ((numchars(a, o, (i-o)+2)
                                               = (1 + numchars(a, o, i-o)))
                                              && (numchars(a, o, (i-o)+2)
                                                  <= numchars(a, o, l))
                                              && (((i-o)+1) < l))
                                           : ((numchars(a, o, (i-o)+1)
                                               = (1 + numchars(a, o, i-o)))
                                              && (numchars(a, o, (i-o)+1)
                                                  <= numchars(a, o, l))))}
  @-}
unsafeIndexF :: Array -> Int -> Int -> Int -> Word16
unsafeIndexF a o l i = let x = unsafeIndex a i
                       in liquidAssume (unsafeIndexFQ x a o l i) x

{-@ unsafeIndexFQ :: x:Data.Word.Word16
                  -> a:Data.Text.Array.Array
                  -> o:Int
                  -> l:Int
                  -> i:Int
                  -> {v:Bool | ((Prop v) <=>
                                (((x >= 55296) && (x <= 56319))
                                 ? ((numchars(a, o, (i-o)+2)
                                     = (1 + numchars(a, o, i-o)))
                                    && (numchars(a, o, (i-o)+2)
                                        <= numchars(a, o, l))
                                    && (((i-o)+1) < l))
                                 : ((numchars(a, o, (i-o)+1)
                                     = (1 + numchars(a, o, i-o)))
                                    && (numchars(a, o, (i-o)+1)
                                        <= numchars(a, o, l)))))}
  @-}
unsafeIndexFQ :: Word16 -> Array -> Int -> Int -> Int -> Bool
unsafeIndexFQ = undefined

{-@ unsafeIndexB :: a:Data.Text.Array.Array
                 -> o:{v:Int | (BtwnI v 0 (alen a))}
                 -> l:{v:Int | ((v >= 0) && ((o+v) <= (alen a)))}
                 -> i:{v:Int | (Btwn (v) (o) (o + l))}
                 -> {v:Data.Word.Word16 | (((v >= 56320) && (v <= 57343))
                                           ? ((numchars(a, o, (i-o)+1)
                                               = (1 + numchars(a, o, (i-o)-1)))
                                              && (numchars(a, o, (i-o-1)) >= 0)
                                              && (((i-o)-1) >= 0))
                                           : ((numchars(a, o, (i-o)+1)
                                               = (1 + numchars(a, o, i-o)))
                                              && (numchars(a, o, (i-o)) >= 0)))}
  @-}
unsafeIndexB :: Array -> Int -> Int -> Int -> Word16
unsafeIndexB a o l i = let x = unsafeIndex a i
                       in liquidAssume (unsafeIndexBQ x a o i) x

{-@ unsafeIndexBQ :: x:Data.Word.Word16
                  -> a:Data.Text.Array.Array
                  -> o:Int
                  -> i:Int
                  -> {v:Bool | ((Prop v) <=>
                                (((x >= 56320) && (x <= 57343))
                                 ? ((numchars(a, o, (i-o)+1)
                                     = (1 + numchars(a, o, (i-o)-1)))
                                    && (numchars(a, o, (i-o-1)) >= 0)
                                    && (((i-o)-1) >= 0))
                                 : ((numchars(a, o, (i-o)+1)
                                     = (1 + numchars(a, o, i-o)))
                                    && (numchars(a, o, (i-o)) >= 0))))}
  @-}
unsafeIndexBQ :: Word16 -> Array -> Int -> Int -> Bool
unsafeIndexBQ = undefined

-- | Unchecked write of a mutable array.  May return garbage or crash
-- on an out-of-bounds access.
{-@ unsafeWrite :: ma:Data.Text.Array.MArray s
                -> i:{v:Nat | v < (malen ma)}
                -> Data.Word.Word16
                -> GHC.ST.ST s ()
  @-}
unsafeWrite :: MArray s -> Int -> Word16 -> ST s ()
unsafeWrite MArray{..} i@(I# i#) (W16# e#) = ST $ \s1# ->
  CHECK_BOUNDS("unsafeWrite",maLen,i)
  case writeWord16Array# maBA i# e# s1# of
    s2# -> (# s2#, () #)
{-# INLINE unsafeWrite #-}

-- | Convert an immutable array to a list.
{-@ toList :: a:Data.Text.Array.Array
           -> o:{v:Nat | v <= (alen a)}
           -> l:{v:Nat | (v + o) <= (alen a)}
           -> {v:[Data.Word.Word16] | (len v) = l}
  @-}
toList :: Array -> Int -> Int -> [Word16]
--LIQUID toList ary off len = loop 0
--LIQUID     where loop i | i < len   = unsafeIndex ary (off+i) : loop (i+1)
--LIQUID                  | otherwise = []
toList ary off len = toList_loop ary off len 0

{-@ toList_loop :: a:Data.Text.Array.Array
                -> o:{v:Nat | v <= (alen a)}
                -> l:{v:Nat | (v + o) <= (alen a)}
                -> i:{v:Nat | v <= l}
                -> {v:[Data.Word.Word16] | (len v) = (l - i)}
  @-}
toList_loop ary off len i
    | i < len   = unsafeIndex ary (off+i) : toList_loop ary off len (i+1)
    | otherwise = []

-- | An empty immutable array.
{-@ empty :: {v:Data.Text.Array.Array | (alen v) = 0} @-}
empty :: Array
empty = runST (new 0 >>= unsafeFreeze)

-- | Run an action in the ST monad and return an immutable array of
-- its result.

{-
run :: forall <p :: Int -> Prop>.
       (forall s. GHC.ST.ST s (Data.Text.Array.MArray s)<p>)
     -> exists[z:Int<p>]. Data.Text.Array.Array<p>
@-}
{- run :: (forall s. GHC.ST.ST s ma:(Data.Text.Array.MArray s))
        -> {v:Data.Text.Array.Array | (alen v) = (len ma)}
  @-}
run :: (forall s. ST s (MArray s)) -> Array
run k = runST (k >>= unsafeFreeze)

-- | Run an action in the ST monad and return an immutable array of
-- its result paired with whatever else the action returns.
{- run2 :: (forall s. GHC.ST.ST s (ma:Data.Text.Array.MArray s, a:a))
         -> ({v:Data.Text.Array.Array | (alen v) = (malen ma)}, {v:a | v = a})
  @-}
run2 :: (forall s. ST s (MArray s, a)) -> (Array, a)
run2 k = runST (do
                 (marr,b) <- k
                 arr <- unsafeFreeze marr
                 return (arr,b))

-- | Copy some elements of a mutable array.
{-@ copyM :: ma1:Data.Text.Array.MArray s
          -> o1:{v:Nat | v <= (malen ma1)}
          -> ma2:Data.Text.Array.MArray s
          -> o2:{v:Nat | v <= (malen ma2)}
          -> cnt:{v:Nat | (((v + o1) <= (malen ma1)) &&
                           ((v + o2) <= (malen ma2)))}
          -> GHC.ST.ST s ()
  @-}
copyM :: MArray s               -- ^ Destination
      -> Int                    -- ^ Destination offset
      -> MArray s               -- ^ Source
      -> Int                    -- ^ Source offset
      -> Int                    -- ^ Count
      -> ST s ()
copyM dest didx src sidx count
    | count <= 0 = return ()
    | otherwise =
--LIQUID #if defined(ASSERTS)
--LIQUID     assert (sidx + count <= length src) .
--LIQUID     assert (didx + count <= length dest) .
--LIQUID #endif
    liquidAssert (sidx + count <= maLen src) .
    liquidAssert (didx + count <= maLen dest) .
    unsafeIOToST $ memcpyM (maBA dest) (fromIntegral didx)
                           (maBA src) (fromIntegral sidx)
                           (fromIntegral count)
{-# INLINE copyM #-}

-- | Copy some elements of an immutable array.
{-@ copyI :: ma:Data.Text.Array.MArray s
          -> mo:{v:Nat | v <= (malen ma)}
          -> a:Data.Text.Array.Array
          -> o:{v:Nat | v <= (alen a)}
          -> top:{v:Int | ((v >= mo)
                           && (v <= (malen ma))
                           && (((v-mo)+o) <= (alen a)))}
          -> GHC.ST.ST s ()
  @-}
copyI :: MArray s               -- ^ Destination
      -> Int                    -- ^ Destination offset
      -> Array                  -- ^ Source
      -> Int                    -- ^ Source offset
      -> Int                    -- ^ First offset in destination /not/ to
                                -- copy (i.e. /not/ length)
      -> ST s ()
copyI dest i0 src j0 top
    | i0 >= top = return ()
    | otherwise = unsafeIOToST $
                  memcpyI (maBA dest) (fromIntegral i0)
                          (aBA src) (fromIntegral j0)
                          (fromIntegral (top-i0))
{-# INLINE copyI #-}

-- | Compare portions of two arrays for equality.  No bounds checking
-- is performed.
{- equal :: a1:Data.Text.Array.Array
          -> o1:{v:Int | ((v >= 0) && (v < (alen a1)))}
          -> a2:Data.Text.Array.Array
          -> o2:{v:Int | ((v >= 0) && (v < (alen a2)))}
          -> cnt:{v:Int | ((v >= 0) && ((v+o1) < (alen a1)) && ((v+o2) < (alen a2)))}
          -> {v:Bool | ((Prop v) <=> (a1 = a2))}
  @-}
equal :: Array                  -- ^ First
      -> Int                    -- ^ Offset into first
      -> Array                  -- ^ Second
      -> Int                    -- ^ Offset into second
      -> Int                    -- ^ Count
      -> Bool
equal arrA offA arrB offB count = inlinePerformIO $ do
  i <- memcmp (aBA arrA) (fromIntegral offA)
                     (aBA arrB) (fromIntegral offB) (fromIntegral count)
  return $! i == 0
{-# INLINE equal #-}

foreign import ccall unsafe "_hs_text_memcpy" memcpyI
    :: MutableByteArray# s -> CSize -> ByteArray# -> CSize -> CSize -> IO ()

{- memcmp :: a1:GHC.Prim.ByteArray#
           -> CSize
           -> a2:GHC.Prim.ByteArray#
           -> CSize
           -> CSize
           -> IO {v:CInt | ((v = 0) <=> (a1 = a2))}
  @-}
foreign import ccall unsafe "_hs_text_memcmp" memcmp
    :: ByteArray# -> CSize -> ByteArray# -> CSize -> CSize -> IO CInt

foreign import ccall unsafe "_hs_text_memcpy" memcpyM
    :: MutableByteArray# s -> CSize -> MutableByteArray# s -> CSize -> CSize
    -> IO ()
