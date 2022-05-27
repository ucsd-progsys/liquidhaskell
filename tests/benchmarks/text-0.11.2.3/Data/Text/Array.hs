{-@ LIQUID "--bscope" @-}
{-@ LIQUID "--no-check-imports" @-}
{- LIQUID "--no-pattern-inline" @-}

{-# LANGUAGE BangPatterns, CPP, ForeignFunctionInterface, MagicHash, Rank2Types,
    RecordWildCards, UnboxedTuples, UnliftedFFITypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
                 indexWord16Array#, newByteArray#, writeWord16Array#)
import GHC.Exts (unsafeCoerce#) -- Importing from GHC.Exts makes this future-proof (i.e. works for GHC >= 9)
import GHC.ST (ST(..), runST)
import GHC.Word (Word16(..))
import Prelude hiding (error, length, read)

--LIQUID
import Language.Haskell.Liquid.Prelude

{-@ predicate Btwn V X Y   = ((X <= V) && (V < Y)) @-}
{-@ predicate BtwnE V X Y  = ((X < V)  && (V < Y)) @-}
{-@ predicate BtwnI V X Y  = ((X <= V) && (V <= Y)) @-}
{-@ predicate BtwnEI V X Y = ((X < V)  && (V <= Y)) @-}

{-@ qualif LenDiff(v:List a, i:int, l:int): (len v) = (l - i) @-}
{-@ qualif Diff(v:int, d:int, l:int): v = l - d @-}

{-@ lazy error @-}
error :: String -> a
error msg = error msg

-- | Immutable array type.
data Array = Array {
      aBA :: ByteArray#
--LIQUID #if defined(ASSERTS)
    , aLen :: {-# UNPACK #-} !Int -- length (in units of Word16, not bytes)
--LIQUID #endif
    }

{-@ data Array = Array { aBA  :: ByteArray#
                       , aLen :: Nat }
  @-}




{-@ type ArrayN N = {v:Array | (aLen v) = N} @-}

{-@ type AValidI A   = {v:Nat | v     <  (aLen A)} @-}
{-@ type AValidO A   = {v:Nat | v     <= (aLen A)} @-}
{-@ type AValidL O A = {v:Nat | (v+O) <= (aLen A)} @-}

{-@ qualif ALen(v:Int, a:Array): v = aLen(a) @-}
{-@ qualif ALen(v:Array, i:Int): i = aLen(v) @-}

{-@ invariant {v:Array | (aLen v) >= 0} @-}

{-@ measure numchars :: Array -> Int -> Int -> Int @-}

-- | Mutable array type, for use in the ST monad.
data MArray s = MArray {
      maBA :: MutableByteArray# s
--LIQUID #if defined(ASSERTS)
    , maLen :: {-# UNPACK #-} !Int -- length (in units of Word16, not bytes)
--LIQUID #endif
    }

{-@ data MArray s = MArray { maBA  :: MutableByteArray# s
                           , maLen :: Nat
                           }
  @-}


{-@ type MArrayN s N = {v:MArray s | (maLen v) = N} @-}

{-@ type MAValidI A   = {v:Nat | v     <  (maLen A)} @-}
{-@ type MAValidO A   = {v:Nat | v     <= (maLen A)} @-}
{-@ type MAValidL O A = {v:Nat | (v+O) <= (maLen A)} @-}

{-@ qualif MALen(v:Int, a:MArray s): v = maLen(a) @-}
{-@ qualif MALen(v:MArray s, i:Int): i = maLen(v) @-}

{-@ invariant {v:MArray s | (maLen v) >= 0} @-}

{-@ qualif FreezeMArr(v:Array, ma:MArray s):
        aLen(v) = maLen(ma)
  @-}

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
{-@ assume new :: n:Nat -> ST s (MArrayN s n) @-}
-- TODO: losing information in cast
new :: Int -> ST s (MArray s)
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
{-@ assume unsafeFreeze :: ma:MArray s -> (ST s (ArrayN (maLen ma))) @-}
-- TODO: losing information in cast
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
{-@ unsafeIndex :: a:Array -> AValidI a -> Word16 @-}
unsafeIndex :: Array -> Int -> Word16
unsafeIndex Array{..} i@(I# i#) =
  CHECK_BOUNDS("unsafeIndex",aLen,i)
    case indexWord16Array# aBA i# of r# -> (W16# r#)
{-# INLINE unsafeIndex #-}

--LIQUID
{-@ predicate SpanChar D A O L I = (((numchars (A) (O) ((I-O)+D)) = (1 + (numchars (A) (O) (I-O))))
                                 && ((numchars (A) (O) ((I-O)+D)) <= (numchars A O L))
                                 && (((I-O)+D) <= L))
  @-}

{-@ unsafeIndexF :: a:Array -> o:AValidO a -> l:AValidL o a
                 -> i:{v:Int | (Btwn (v) (o) (o + l))}
                 -> {v:Word16 | (if (BtwnI v 55296 56319)
                                 then (SpanChar 2 a o l i)
                                 else (SpanChar 1 a o l i))}
  @-}
unsafeIndexF :: Array -> Int -> Int -> Int -> Word16
unsafeIndexF a o l i = let x = unsafeIndex a i
                       in liquidAssume (unsafeIndexFQ x a o l i) x

{-@ unsafeIndexFQ :: x:Word16 -> a:Array -> o:Int -> l:Int -> i:Int
                  -> {v:Bool | (v <=> (if (BtwnI x 55296 56319)
                                              then (SpanChar 2 a o l i)
                                              else (SpanChar 1 a o l i)))}
  @-}
unsafeIndexFQ :: Word16 -> Array -> Int -> Int -> Int -> Bool
unsafeIndexFQ = undefined

{-@ unsafeIndexB :: a:Array -> o:AValidO a -> l:AValidL o a
                 -> i:{v:Int | Btwn v o (o + l)}
                 -> {v:Word16 | (
       if (v >= 56320 && v <= 57343)
       then ( (numchars a o ((i - o)+1)) = (1 + (numchars a o ((i-o)-1)))
         && ( (numchars a o (i-o-1)) >= 0)
         && ( ((i-o)-1) >= 0))
       else ( ((numchars a o ((i-o)+1)) = (1 + (numchars a o (i-o))))
         && ( (numchars a o (i-o)) >= 0)))}
  @-}
unsafeIndexB :: Array -> Int -> Int -> Int -> Word16
unsafeIndexB a o l i = let x = unsafeIndex a i
                       in liquidAssume (unsafeIndexBQ x a o i) x

{-@ unsafeIndexBQ :: x:Word16 -> a:Array -> o:Int -> i:Int
                  -> {v:Bool | (v <=>
       if (x >= 56320 && x <= 57343)
       then ( (numchars a o ((i - o)+1)) = (1 + (numchars a o ((i-o)-1)))
         && ( (numchars a o (i-o-1)) >= 0)
         && ( ((i-o)-1) >= 0))
       else ( ((numchars a o ((i-o)+1)) = (1 + (numchars a o (i-o))))
         && ( (numchars a o (i-o)) >= 0)))}
  @-}
unsafeIndexBQ :: Word16 -> Array -> Int -> Int -> Bool
unsafeIndexBQ = undefined

-- | Unchecked write of a mutable array.  May return garbage or crash
-- on an out-of-bounds access.
{-@ unsafeWrite :: ma:MArray s -> MAValidI ma -> Word16 -> ST s () @-}
unsafeWrite :: MArray s -> Int -> Word16 -> ST s ()
unsafeWrite MArray{..} i@(I# i#) (W16# e#) = ST $ \s1# ->
  CHECK_BOUNDS("unsafeWrite",maLen,i)
  case writeWord16Array# maBA i# e# s1# of
    s2# -> (# s2#, () #)
{-# INLINE unsafeWrite #-}

-- | Convert an immutable array to a list.
{-@ toList :: a:Array -> o:AValidO a -> l:AValidL o a -> {v:[Word16] | (len v) = l} @-}
toList :: Array -> Int -> Int -> [Word16]
toList ary off len = loop len 0
          {- LIQUID WITNESS -}
    where loop (d :: Int) i
              | i < len   = unsafeIndex ary (off+i) : loop (d-1) (i+1)
              | otherwise = []

-- | An empty immutable array.
{-@ empty :: {v:Array | (aLen v) = 0}  @-}
empty :: Array
empty = runST (new 0 >>= unsafeFreeze)

-- | Run an action in the ST monad and return an immutable array of
-- its result.

{-
run :: forall <p :: Int -> Bool>.
       (forall s. GHC.ST.ST s (Data.Text.Array.MArray s)<p>)
     -> exists[z:Int<p>]. Data.Text.Array.Array<p>
@-}
{- run :: (forall s. GHC.ST.ST s ma:(Data.Text.Array.MArray s))
        -> {v:Data.Text.Array.Array | (aLen v) = (len ma)}
  @-}
run :: (forall s. ST s (MArray s)) -> Array
run k = runST (k >>= unsafeFreeze)

-- | Run an action in the ST monad and return an immutable array of
-- its result paired with whatever else the action returns.
{- run2 :: (forall s. GHC.ST.ST s (ma:Data.Text.Array.MArray s, a:a))
         -> ({v:Data.Text.Array.Array | (aLen v) = (maLen ma)}, {v:a | v = a})
  @-}
run2 :: (forall s. ST s (MArray s, a)) -> (Array, a)
run2 k = runST (do
                 (marr,b) <- k
                 arr <- unsafeFreeze marr
                 return (arr,b))

-- | Copy some elements of a mutable array.
{-@ copyM :: dest:MArray s -> didx:MAValidO dest
          -> src:MArray s  -> sidx:MAValidO src
          -> {v:Nat | (((v + didx) <= (maLen dest))
                    && ((v + sidx) <= (maLen src)))}
          -> ST s ()
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
{-@ copyI :: dest:MArray s -> i0:MAValidO dest
          -> src:Array     -> j0:AValidO src
          -> top:{v:MAValidO dest | ((v-i0)+j0) <= (aLen src)}
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
--LIQUID TODO: this is not correct because we're just comparing sub-arrays
{- equal :: a1:Data.Text.Array.Array
          -> o1:{v:Int | ((v >= 0) && (v < (aLen a1)))}
          -> a2:Data.Text.Array.Array
          -> o2:{v:Int | ((v >= 0) && (v < (aLen a2)))}
          -> cnt:{v:Int | ((v >= 0) && ((v+o1) < (aLen a1)) && ((v+o2) < (aLen a2)))}
          -> {v:Bool | (v <=> (a1 = a2))}
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
{-@ memcpyI :: MutableByteArray# s -> CSize -> ByteArray# -> CSize -> CSize -> IO () @-}

foreign import ccall unsafe "_hs_text_memcmp" memcmp
    :: ByteArray# -> CSize -> ByteArray# -> CSize -> CSize -> IO CInt
{-@ memcmp :: ByteArray# -> CSize -> ByteArray# -> CSize -> CSize -> IO CInt @-}

foreign import ccall unsafe "_hs_text_memcpy" memcpyM
    :: MutableByteArray# s -> CSize -> MutableByteArray# s -> CSize -> CSize
    -> IO ()
{-@ memcpyM :: MutableByteArray# s -> CSize -> MutableByteArray# s -> CSize -> CSize -> IO () @-}
