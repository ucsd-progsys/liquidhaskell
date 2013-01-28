{-# LANGUAGE CPP, ForeignFunctionInterface #-}
-- We cannot actually specify all the language pragmas, see ghc ticket #
-- If we could, these are what they would be:
{- LANGUAGE UnliftedFFITypes, MagicHash,
            UnboxedTuples, DeriveDataTypeable -}
{-# OPTIONS_HADDOCK hide #-}

-- |
-- Module      : Data.ByteString.Internal
-- License     : BSD-style
-- Maintainer  : Don Stewart <dons@galois.com>
-- Stability   : experimental
-- Portability : portable
--
-- A module containing semi-public 'ByteString' internals. This exposes the
-- 'ByteString' representation and low level construction functions. As such
-- all the functions in this module are unsafe. The API is also not stable.
--
-- Where possible application should instead use the functions from the normal
-- public interface modules, such as "Data.ByteString.Unsafe". Packages that
-- extend the ByteString system at a low level will need to use this module.
--
module Data.ByteString.Internal (

        -- * The @ByteString@ type and representation
        ByteString(..),         -- instances: Eq, Ord, Show, Read, Data, Typeable

        -- * Low level introduction and elimination
       create,                 -- :: Int -> (Ptr Word8 -> IO ()) -> IO ByteString
       createAndTrim,          -- :: Int -> (Ptr Word8 -> IO Int) -> IO  ByteString
       createAndTrim',         -- :: Int -> (Ptr Word8 -> IO (Int, Int, a)) -> IO (ByteString, a)
       unsafeCreate,           -- :: Int -> (Ptr Word8 -> IO ()) ->  ByteString
       mallocByteString,       -- :: Int -> IO (ForeignPtr a)

       -- * Conversion to and from ForeignPtrs
       fromForeignPtr,         -- :: ForeignPtr Word8 -> Int -> Int -> ByteString
       toForeignPtr,           -- :: ByteString -> (ForeignPtr Word8, Int, Int)

       -- * Utilities
       inlinePerformIO,        -- :: IO a -> a
       nullForeignPtr,         -- :: ForeignPtr Word8

       -- * Standard C Functions
       c_strlen,               -- :: CString -> IO CInt
       c_free_finalizer,       -- :: FunPtr (Ptr Word8 -> IO ())

       memchr,                 -- :: Ptr Word8 -> Word8 -> CSize -> IO Ptr Word8
       memcmp,                 -- :: Ptr Word8 -> Ptr Word8 -> CSize -> IO CInt
       memcpy,                 -- :: Ptr Word8 -> Ptr Word8 -> CSize -> IO ()
       memset,                 -- :: Ptr Word8 -> Word8 -> CSize -> IO (Ptr Word8)

       -- * cbits functions
-- LIQUID        c_reverse,              -- :: Ptr Word8 -> Ptr Word8 -> CInt -> IO ()
-- LIQUID        c_intersperse,          -- :: Ptr Word8 -> Ptr Word8 -> CInt -> Word8 -> IO ()
-- LIQUID        c_maximum,              -- :: Ptr Word8 -> CInt -> IO Word8
-- LIQUID        c_minimum,              -- :: Ptr Word8 -> CInt -> IO Word8
-- LIQUID        c_count,                -- :: Ptr Word8 -> CInt -> Word8 -> IO CInt
-- LIQUID#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 611
-- LIQUID        -- * Internal GHC magic
-- LIQUID        memcpy_ptr_baoff,       -- :: Ptr a -> RawBuffer -> CInt -> CSize -> IO (Ptr ())
-- LIQUID#endif

       -- * Chars
       w2c, c2w, isSpaceWord8, isSpaceChar8

  ) where

import Foreign.ForeignPtr       (ForeignPtr, withForeignPtr)
import Foreign.Ptr              (Ptr, FunPtr, plusPtr)
import Foreign.Storable         (Storable(..))
import Foreign.C.Types          (CInt(..), CSize(..), CULong(..))
import Foreign.C.String         (CString)

#ifndef __NHC__
import Control.Exception        (assert)
#endif

import Data.Char                (ord)
import Data.Word                (Word8)

#if defined(__GLASGOW_HASKELL__)
import Data.Typeable            (Typeable)
#if __GLASGOW_HASKELL__ >= 610
import Data.Data                (Data)
#else
import Data.Generics            (Data)
#endif
-- LIQUID import GHC.Base                 (realWorld#,unsafeChr)
import GHC.Base                 (unsafeChr) -- LIQUID
import GHC.Int                  (Int32) -- LIQUID
#if __GLASGOW_HASKELL__ >= 611
import GHC.IO                   (IO(IO))
#else
import GHC.IOBase               (IO(IO),RawBuffer)
#endif
#if __GLASGOW_HASKELL__ >= 611
import GHC.IO                   (unsafeDupablePerformIO)
#else
import GHC.IOBase               (unsafeDupablePerformIO)
#endif
#else
import Data.Char                (chr)
import System.IO.Unsafe         (unsafePerformIO)
#endif

import System.IO.Unsafe         (unsafePerformIO) -- LIQUID

#ifdef __GLASGOW_HASKELL__
import GHC.ForeignPtr           (mallocPlainForeignPtrBytes)
#else
import Foreign.ForeignPtr       (mallocForeignPtrBytes)
#endif

#ifdef __GLASGOW_HASKELL__
import GHC.ForeignPtr           (ForeignPtr(ForeignPtr))
-- LIQUID import GHC.Base                 (nullAddr#)
#else
import Foreign.Ptr              (nullPtr)
#endif

import Foreign.Ptr              (nullPtr) -- LIQUID

#if __HUGS__
import Hugs.ForeignPtr          (newForeignPtr_)
#elif __GLASGOW_HASKELL__<=604
import Foreign.ForeignPtr       (newForeignPtr_)
#endif
import Foreign.ForeignPtr       (newForeignPtr_) -- LIQUID 

-- CFILES stuff is Hugs only
{-# CFILES cbits/fpstring.c #-}
{-@ embed Int32        as int    @-}
{-@ embed CInt         as int    @-}
{-@ embed CSize        as Word32 @-}
-- An alternative to Control.Exception (assert) for nhc98
#ifdef __NHC__
#define assert	assertS "__FILE__ : __LINE__"
assertS :: String -> Bool -> a -> a
assertS _ True  = id
assertS s False = error ("assertion failed at "++s)
#endif
-- -----------------------------------------------------------------------------
--
-- Useful macros, until we have bang patterns
--

#define STRICT1(f) f a | a `seq` False = undefined
#define STRICT2(f) f a b | a `seq` b `seq` False = undefined
#define STRICT3(f) f a b c | a `seq` b `seq` c `seq` False = undefined
#define STRICT4(f) f a b c d | a `seq` b `seq` c `seq` d `seq` False = undefined
#define STRICT5(f) f a b c d e | a `seq` b `seq` c `seq` d `seq` e `seq` False = undefined

-- -----------------------------------------------------------------------------

-- | A space-efficient representation of a Word8 vector, supporting many
-- efficient operations.  A 'ByteString' contains 8-bit characters only.
--
-- Instances of Eq, Ord, Read, Show, Data, Typeable
--
data ByteString = PS {-# UNPACK #-} !(ForeignPtr Word8) -- payload
                     {-# UNPACK #-} !Int                -- offset
                     {-# UNPACK #-} !Int                -- length
-- LIQUID #if defined(__GLASGOW_HASKELL__)
-- LIQUID     deriving (Data, Typeable)
-- LIQUID #endif

-- LIQUID instance Show ByteString where
-- LIQUID     showsPrec p ps r = showsPrec p (unpackWith w2c ps) r

-- LIQUID instance Read ByteString where
-- LIQUID     readsPrec p str = [ (packWith c2w x, y) | (x, y) <- readsPrec p str ]

-- | /O(n)/ Converts a 'ByteString' to a '[a]', using a conversion function.
unpackWith :: (Word8 -> a) -> ByteString -> [a]
unpackWith _ (PS _  _ 0) = []
unpackWith k (PS ps s l) = inlinePerformIO $ withForeignPtr ps $ \p ->
        go (p `plusPtr` s) (l - 1) []
    where
        STRICT3(go)
        go p 0 acc = peek p          >>= \e -> return (k e : acc)
        go p n acc = peekByteOff p n >>= \e -> go p (n-1) (k e : acc)
{-# INLINE unpackWith #-}

-- | /O(n)/ Convert a '[a]' into a 'ByteString' using some
-- conversion function
packWith :: (a -> Word8) -> [a] -> ByteString
packWith k str = unsafeCreate (length str) $ \p -> go p str
    where
        STRICT2(go)
        go _ []     = return ()
        go p (x:xs) = poke p (k x) >> go (p `plusPtr` 1) xs -- less space than pokeElemOff
{-# INLINE packWith #-}

------------------------------------------------------------------------
-- | The 0 pointer. Used to indicate the empty Bytestring.
nullForeignPtr :: ForeignPtr Word8
-- LIQUID #ifdef __GLASGOW_HASKELL__
-- LIQUID nullForeignPtr = ForeignPtr nullAddr# undefined --TODO: should ForeignPtrContents be strict?
-- LIQUID #else
nullForeignPtr = unsafePerformIO $ newForeignPtr_ nullPtr
{-# NOINLINE nullForeignPtr #-}
-- LIQUID #endif
-- LIQUID 
-- ---------------------------------------------------------------------
-- Low level constructors

-- | /O(1)/ Build a ByteString from a ForeignPtr.
--
-- If you do not need the offset parameter then you do should be using
-- 'Data.ByteString.Unsafe.unsafePackCStringLen' or
-- 'Data.ByteString.Unsafe.unsafePackCStringFinalizer' instead.
--
fromForeignPtr :: ForeignPtr Word8
               -> Int -- ^ Offset
               -> Int -- ^ Length
               -> ByteString
fromForeignPtr fp s l = PS fp s l
{-# INLINE fromForeignPtr #-}

-- | /O(1)/ Deconstruct a ForeignPtr from a ByteString
toForeignPtr :: ByteString -> (ForeignPtr Word8, Int, Int) -- ^ (ptr, offset, length)
toForeignPtr (PS ps s l) = (ps, s, l)
{-# INLINE toForeignPtr #-}

-- | A way of creating ByteStrings outside the IO monad. The @Int@
-- argument gives the final size of the ByteString. Unlike
-- 'createAndTrim' the ByteString is not reallocated if the final size
-- is less than the estimated size.
unsafeCreate :: Int -> (Ptr Word8 -> IO ()) -> ByteString
unsafeCreate l f = unsafeDupablePerformIO (create l f)
{-# INLINE unsafeCreate #-}

#ifndef __GLASGOW_HASKELL__
-- for Hugs, NHC etc
unsafeDupablePerformIO :: IO a -> a
unsafeDupablePerformIO = unsafePerformIO
#endif

-- | Create ByteString of size @l@ and use action @f@ to fill it's contents.
create :: Int -> (Ptr Word8 -> IO ()) -> IO ByteString
create l f = do
    fp <- mallocByteString l
    withForeignPtr fp $ \p -> f p
    return $! PS fp 0 l
{-# INLINE create #-}

-- | Given the maximum size needed and a function to make the contents
-- of a ByteString, createAndTrim makes the 'ByteString'. The generating
-- function is required to return the actual final size (<= the maximum
-- size), and the resulting byte array is realloced to this size.
--
-- createAndTrim is the main mechanism for creating custom, efficient
-- ByteString functions, using Haskell or C functions to fill the space.
--
createAndTrim :: Int -> (Ptr Word8 -> IO Int) -> IO ByteString
createAndTrim l f = do
    fp <- mallocByteString l
    withForeignPtr fp $ \p -> do
        l' <- f p
        if assert (l' <= l) $ l' >= l
            then return $! PS fp 0 l
            else create l' $ \p' -> memcpy p' p (fromIntegral l')
{-# INLINE createAndTrim #-}

createAndTrim' :: Int -> (Ptr Word8 -> IO (Int, Int, a)) -> IO (ByteString, a)
createAndTrim' l f = do
    fp <- mallocByteString l
    withForeignPtr fp $ \p -> do
        (off, l', res) <- f p
        if assert (l' <= l) $ l' >= l
            then return $! (PS fp 0 l, res)
            else do ps <- create l' $ \p' ->
                            memcpy p' (p `plusPtr` off) (fromIntegral l')
                    return $! (ps, res)

-- | Wrapper of 'mallocForeignPtrBytes' with faster implementation for GHC
--
mallocByteString :: Int -> IO (ForeignPtr a)
mallocByteString l = do
#ifdef __GLASGOW_HASKELL__
    mallocPlainForeignPtrBytes l
#else
    mallocForeignPtrBytes l
#endif
{-# INLINE mallocByteString #-}

------------------------------------------------------------------------

-- | Conversion between 'Word8' and 'Char'. Should compile to a no-op.
w2c :: Word8 -> Char
#if !defined(__GLASGOW_HASKELL__)
w2c = chr . fromIntegral
#else
w2c = unsafeChr . fromIntegral
#endif
{-# INLINE w2c #-}

-- | Unsafe conversion between 'Char' and 'Word8'. This is a no-op and
-- silently truncates to 8 bits Chars > '\255'. It is provided as
-- convenience for ByteString construction.
c2w :: Char -> Word8
c2w = fromIntegral . ord
{-# INLINE c2w #-}

-- | Selects words corresponding to white-space characters in the Latin-1 range
-- ordered by frequency. 
isSpaceWord8 :: Word8 -> Bool
isSpaceWord8 w =
    w == 0x20 ||
    w == 0x0A || -- LF, \n
    w == 0x09 || -- HT, \t
    w == 0x0C || -- FF, \f
    w == 0x0D || -- CR, \r
    w == 0x0B || -- VT, \v
    w == 0xA0    -- spotted by QC..
{-# INLINE isSpaceWord8 #-}

-- | Selects white-space characters in the Latin-1 range
isSpaceChar8 :: Char -> Bool
isSpaceChar8 c =
    c == ' '     ||
    c == '\t'    ||
    c == '\n'    ||
    c == '\r'    ||
    c == '\f'    ||
    c == '\v'    ||
    c == '\xa0'
{-# INLINE isSpaceChar8 #-}

------------------------------------------------------------------------

-- | Just like unsafePerformIO, but we inline it. Big performance gains as
-- it exposes lots of things to further inlining. /Very unsafe/. In
-- particular, you should do no memory allocation inside an
-- 'inlinePerformIO' block. On Hugs this is just @unsafePerformIO@.
--
{-# INLINE inlinePerformIO #-}
inlinePerformIO :: IO a -> a
-- LIQUID #if defined(__GLASGOW_HASKELL__)
-- LIQUID inlinePerformIO (IO m) = case m realWorld# of (# _, r #) -> r
-- LIQUID #else
inlinePerformIO = unsafePerformIO
-- LIQUID #endif

-- ---------------------------------------------------------------------
-- 
-- Standard C functions
--

foreign import ccall unsafe "string.h strlen" c_strlen
    :: CString -> IO CSize

foreign import ccall unsafe "static stdlib.h &free" c_free_finalizer
    :: FunPtr (Ptr Word8 -> IO ())

foreign import ccall unsafe "string.h memchr" c_memchr
    :: Ptr Word8 -> CInt -> CSize -> IO (Ptr Word8)

memchr :: Ptr Word8 -> Word8 -> CSize -> IO (Ptr Word8)
memchr p w s = c_memchr p (fromIntegral w) s

foreign import ccall unsafe "string.h memcmp" memcmp
    :: Ptr Word8 -> Ptr Word8 -> CSize -> IO CInt

foreign import ccall unsafe "string.h memcpy" c_memcpy
    :: Ptr Word8 -> Ptr Word8 -> CSize -> IO (Ptr Word8)

memcpy = undefined -- LIQUID 
-- LIQUID memcpy :: Ptr Word8 -> Ptr Word8 -> CSize -> IO ()
-- LIQUID memcpy p q s = c_memcpy p q s >> return ()

{-
foreign import ccall unsafe "string.h memmove" c_memmove
    :: Ptr Word8 -> Ptr Word8 -> CSize -> IO (Ptr Word8)

memmove :: Ptr Word8 -> Ptr Word8 -> CSize -> IO ()
memmove p q s = do c_memmove p q s
                   return ()
-}

foreign import ccall unsafe "string.h memset" c_memset
    :: Ptr Word8 -> CInt -> CSize -> IO (Ptr Word8)

memset :: Ptr Word8 -> Word8 -> CSize -> IO (Ptr Word8)
memset p w s = c_memset p (fromIntegral w) s
-- ---------------------------------------------------------------------
--
-- Uses our C code
--

foreign import ccall unsafe "static fpstring.h fps_reverse" c_reverse
    :: Ptr Word8 -> Ptr Word8 -> CULong -> IO ()

foreign import ccall unsafe "static fpstring.h fps_intersperse" c_intersperse
    :: Ptr Word8 -> Ptr Word8 -> CULong -> Word8 -> IO ()

foreign import ccall unsafe "static fpstring.h fps_maximum" c_maximum
    :: Ptr Word8 -> CULong -> IO Word8

foreign import ccall unsafe "static fpstring.h fps_minimum" c_minimum
    :: Ptr Word8 -> CULong -> IO Word8

foreign import ccall unsafe "static fpstring.h fps_count" c_count
    :: Ptr Word8 -> CULong -> Word8 -> IO CULong

-- ---------------------------------------------------------------------
-- Internal GHC Haskell magic

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 611
foreign import ccall unsafe "__hscore_memcpy_src_off"
   memcpy_ptr_baoff :: Ptr a -> RawBuffer -> CInt -> CSize -> IO (Ptr ())
#endif
