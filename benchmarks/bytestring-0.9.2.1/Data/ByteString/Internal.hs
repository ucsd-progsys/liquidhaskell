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
-- LIQUID        createAndTrim,          -- :: Int -> (Ptr Word8 -> IO Int) -> IO  ByteString
-- LIQUID        createAndTrim',         -- :: Int -> (Ptr Word8 -> IO (Int, Int, a)) -> IO (ByteString, a)
-- LIQUID        unsafeCreate,           -- :: Int -> (Ptr Word8 -> IO ()) ->  ByteString
-- LIQUID        mallocByteString,       -- :: Int -> IO (ForeignPtr a)
-- LIQUID
-- LIQUID        -- * Conversion to and from ForeignPtrs
-- LIQUID        fromForeignPtr,         -- :: ForeignPtr Word8 -> Int -> Int -> ByteString
-- LIQUID        toForeignPtr,           -- :: ByteString -> (ForeignPtr Word8, Int, Int)
-- LIQUID
-- LIQUID        -- * Utilities
-- LIQUID        inlinePerformIO,        -- :: IO a -> a
-- LIQUID        nullForeignPtr,         -- :: ForeignPtr Word8
-- LIQUID
-- LIQUID        -- * Standard C Functions
-- LIQUID        c_strlen,               -- :: CString -> IO CInt
-- LIQUID        c_free_finalizer,       -- :: FunPtr (Ptr Word8 -> IO ())
-- LIQUID
-- LIQUID        memchr,                 -- :: Ptr Word8 -> Word8 -> CSize -> IO Ptr Word8
-- LIQUID        memcmp,                 -- :: Ptr Word8 -> Ptr Word8 -> CSize -> IO CInt
-- LIQUID        memcpy,                 -- :: Ptr Word8 -> Ptr Word8 -> CSize -> IO ()
-- LIQUID        memset,                 -- :: Ptr Word8 -> Word8 -> CSize -> IO (Ptr Word8)
-- LIQUID
-- LIQUID        -- * cbits functions
-- LIQUID        c_reverse,              -- :: Ptr Word8 -> Ptr Word8 -> CInt -> IO ()
-- LIQUID        c_intersperse,          -- :: Ptr Word8 -> Ptr Word8 -> CInt -> Word8 -> IO ()
-- LIQUID        c_maximum,              -- :: Ptr Word8 -> CInt -> IO Word8
-- LIQUID        c_minimum,              -- :: Ptr Word8 -> CInt -> IO Word8
-- LIQUID        c_count,                -- :: Ptr Word8 -> CInt -> Word8 -> IO CInt
-- LIQUID#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 611
-- LIQUID        -- * Internal GHC magic
-- LIQUID        memcpy_ptr_baoff,       -- :: Ptr a -> RawBuffer -> CInt -> CSize -> IO (Ptr ())
-- LIQUID#endif
-- LIQUID
-- LIQUID        -- * Chars
-- LIQUID        w2c, c2w, isSpaceWord8, isSpaceChar8
-- LIQUID
  ) where

import Foreign.ForeignPtr       (ForeignPtr, withForeignPtr)
import Foreign.Ptr              (Ptr, FunPtr, plusPtr)
import Foreign.Storable         (Storable(..))
import Foreign.C.Types          (CInt(..), CSize(..), CULong(..))
import Foreign.C.String         (CString)

-- LIQUID #ifndef __NHC__
-- LIQUID import Control.Exception        (assert)
-- LIQUID #endif
-- LIQUID 
-- LIQUID import Data.Char                (ord)
import Data.Word                (Word8)
-- LIQUID 
-- LIQUID #if defined(__GLASGOW_HASKELL__)
-- LIQUID import Data.Typeable            (Typeable)
-- LIQUID #if __GLASGOW_HASKELL__ >= 610
-- LIQUID import Data.Data                (Data)
-- LIQUID #else
-- LIQUID import Data.Generics            (Data)
-- LIQUID #endif
-- LIQUID import GHC.Base                 (realWorld#,unsafeChr)
-- LIQUID #if __GLASGOW_HASKELL__ >= 611
-- LIQUID import GHC.IO                   (IO(IO))
-- LIQUID #else
-- LIQUID import GHC.IOBase               (IO(IO),RawBuffer)
-- LIQUID #endif
-- LIQUID #if __GLASGOW_HASKELL__ >= 611
-- LIQUID import GHC.IO                   (unsafeDupablePerformIO)
-- LIQUID #else
-- LIQUID import GHC.IOBase               (unsafeDupablePerformIO)
-- LIQUID #endif
-- LIQUID #else
-- LIQUID import Data.Char                (chr)
-- LIQUID import System.IO.Unsafe         (unsafePerformIO)
-- LIQUID #endif
-- LIQUID 
#ifdef __GLASGOW_HASKELL__
import GHC.ForeignPtr           (mallocPlainForeignPtrBytes)
#else
import Foreign.ForeignPtr       (mallocForeignPtrBytes)
#endif

-- LIQUID #ifdef __GLASGOW_HASKELL__
-- LIQUID import GHC.ForeignPtr           (ForeignPtr(ForeignPtr))
-- LIQUID import GHC.Base                 (nullAddr#)
-- LIQUID #else
-- LIQUID import Foreign.Ptr              (nullPtr)
-- LIQUID #endif
-- LIQUID 
-- LIQUID #if __HUGS__
-- LIQUID import Hugs.ForeignPtr          (newForeignPtr_)
-- LIQUID #elif __GLASGOW_HASKELL__<=604
-- LIQUID import Foreign.ForeignPtr       (newForeignPtr_)
-- LIQUID #endif

-- CFILES stuff is Hugs only
-- LIQUID {-# CFILES cbits/fpstring.c #-}
-- LIQUID 
-- LIQUID -- An alternative to Control.Exception (assert) for nhc98
-- LIQUID #ifdef __NHC__
-- LIQUID #define assert	assertS "__FILE__ : __LINE__"
-- LIQUID assertS :: String -> Bool -> a -> a
-- LIQUID assertS _ True  = id
-- LIQUID assertS s False = error ("assertion failed at "++s)
-- LIQUID #endif
-- LIQUID 
-- LIQUID -- -----------------------------------------------------------------------------
-- LIQUID --
-- LIQUID -- Useful macros, until we have bang patterns
-- LIQUID --
-- LIQUID 
-- LIQUID #define STRICT1(f) f a | a `seq` False = undefined
-- LIQUID #define STRICT2(f) f a b | a `seq` b `seq` False = undefined
-- LIQUID #define STRICT3(f) f a b c | a `seq` b `seq` c `seq` False = undefined
-- LIQUID #define STRICT4(f) f a b c d | a `seq` b `seq` c `seq` d `seq` False = undefined
-- LIQUID #define STRICT5(f) f a b c d e | a `seq` b `seq` c `seq` d `seq` e `seq` False = undefined
-- LIQUID 
-- LIQUID -- -----------------------------------------------------------------------------
-- LIQUID 
-- LIQUID -- | A space-efficient representation of a Word8 vector, supporting many
-- LIQUID -- efficient operations.  A 'ByteString' contains 8-bit characters only.
-- LIQUID --
-- LIQUID -- Instances of Eq, Ord, Read, Show, Data, Typeable
-- LIQUID --
data ByteString = PS {-# UNPACK #-} !(ForeignPtr Word8) -- payload
                     {-# UNPACK #-} !Int                -- offset
                     {-# UNPACK #-} !Int                -- length
-- LIQUID 
-- LIQUID #if defined(__GLASGOW_HASKELL__)
-- LIQUID     deriving (Data, Typeable)
-- LIQUID #endif
-- LIQUID 
-- LIQUID instance Show ByteString where
-- LIQUID     showsPrec p ps r = showsPrec p (unpackWith w2c ps) r
-- LIQUID 
-- LIQUID instance Read ByteString where
-- LIQUID     readsPrec p str = [ (packWith c2w x, y) | (x, y) <- readsPrec p str ]
-- LIQUID 
-- LIQUID -- | /O(n)/ Converts a 'ByteString' to a '[a]', using a conversion function.
-- LIQUID unpackWith :: (Word8 -> a) -> ByteString -> [a]
-- LIQUID unpackWith _ (PS _  _ 0) = []
-- LIQUID unpackWith k (PS ps s l) = inlinePerformIO $ withForeignPtr ps $ \p ->
-- LIQUID         go (p `plusPtr` s) (l - 1) []
-- LIQUID     where
-- LIQUID         STRICT3(go)
-- LIQUID         go p 0 acc = peek p          >>= \e -> return (k e : acc)
-- LIQUID         go p n acc = peekByteOff p n >>= \e -> go p (n-1) (k e : acc)
-- LIQUID {-# INLINE unpackWith #-}
-- LIQUID 
-- LIQUID -- | /O(n)/ Convert a '[a]' into a 'ByteString' using some
-- LIQUID -- conversion function
-- LIQUID packWith :: (a -> Word8) -> [a] -> ByteString
-- LIQUID packWith k str = unsafeCreate (length str) $ \p -> go p str
-- LIQUID     where
-- LIQUID         STRICT2(go)
-- LIQUID         go _ []     = return ()
-- LIQUID         go p (x:xs) = poke p (k x) >> go (p `plusPtr` 1) xs -- less space than pokeElemOff
-- LIQUID {-# INLINE packWith #-}
-- LIQUID 
-- LIQUID ------------------------------------------------------------------------
-- LIQUID 
-- LIQUID -- | The 0 pointer. Used to indicate the empty Bytestring.
-- LIQUID nullForeignPtr :: ForeignPtr Word8
-- LIQUID #ifdef __GLASGOW_HASKELL__
-- LIQUID nullForeignPtr = ForeignPtr nullAddr# undefined --TODO: should ForeignPtrContents be strict?
-- LIQUID #else
-- LIQUID nullForeignPtr = unsafePerformIO $ newForeignPtr_ nullPtr
-- LIQUID {-# NOINLINE nullForeignPtr #-}
-- LIQUID #endif
-- LIQUID 
-- LIQUID -- ---------------------------------------------------------------------
-- LIQUID -- Low level constructors
-- LIQUID 
-- LIQUID -- | /O(1)/ Build a ByteString from a ForeignPtr.
-- LIQUID --
-- LIQUID -- If you do not need the offset parameter then you do should be using
-- LIQUID -- 'Data.ByteString.Unsafe.unsafePackCStringLen' or
-- LIQUID -- 'Data.ByteString.Unsafe.unsafePackCStringFinalizer' instead.
-- LIQUID --
-- LIQUID fromForeignPtr :: ForeignPtr Word8
-- LIQUID                -> Int -- ^ Offset
-- LIQUID                -> Int -- ^ Length
-- LIQUID                -> ByteString
-- LIQUID fromForeignPtr fp s l = PS fp s l
-- LIQUID {-# INLINE fromForeignPtr #-}
-- LIQUID 
-- LIQUID -- | /O(1)/ Deconstruct a ForeignPtr from a ByteString
-- LIQUID toForeignPtr :: ByteString -> (ForeignPtr Word8, Int, Int) -- ^ (ptr, offset, length)
-- LIQUID toForeignPtr (PS ps s l) = (ps, s, l)
-- LIQUID {-# INLINE toForeignPtr #-}
-- LIQUID 
-- LIQUID -- | A way of creating ByteStrings outside the IO monad. The @Int@
-- LIQUID -- argument gives the final size of the ByteString. Unlike
-- LIQUID -- 'createAndTrim' the ByteString is not reallocated if the final size
-- LIQUID -- is less than the estimated size.
-- LIQUID unsafeCreate :: Int -> (Ptr Word8 -> IO ()) -> ByteString
-- LIQUID unsafeCreate l f = unsafeDupablePerformIO (create l f)
-- LIQUID {-# INLINE unsafeCreate #-}
-- LIQUID 
-- LIQUID #ifndef __GLASGOW_HASKELL__
-- LIQUID -- for Hugs, NHC etc
-- LIQUID unsafeDupablePerformIO :: IO a -> a
-- LIQUID unsafeDupablePerformIO = unsafePerformIO
-- LIQUID #endif
-- LIQUID 
-- | Create ByteString of size @l@ and use action @f@ to fill it's contents.
create :: Int -> (Ptr Word8 -> IO ()) -> IO ByteString
create l f = do
    fp <- mallocByteString l
    withForeignPtr fp $ \p -> f p
    return $! PS fp 0 l
{-# INLINE create #-}

-- LIQUID -- | Given the maximum size needed and a function to make the contents
-- LIQUID -- of a ByteString, createAndTrim makes the 'ByteString'. The generating
-- LIQUID -- function is required to return the actual final size (<= the maximum
-- LIQUID -- size), and the resulting byte array is realloced to this size.
-- LIQUID --
-- LIQUID -- createAndTrim is the main mechanism for creating custom, efficient
-- LIQUID -- ByteString functions, using Haskell or C functions to fill the space.
-- LIQUID --
-- LIQUID createAndTrim :: Int -> (Ptr Word8 -> IO Int) -> IO ByteString
-- LIQUID createAndTrim l f = do
-- LIQUID     fp <- mallocByteString l
-- LIQUID     withForeignPtr fp $ \p -> do
-- LIQUID         l' <- f p
-- LIQUID         if assert (l' <= l) $ l' >= l
-- LIQUID             then return $! PS fp 0 l
-- LIQUID             else create l' $ \p' -> memcpy p' p (fromIntegral l')
-- LIQUID {-# INLINE createAndTrim #-}
-- LIQUID 
-- LIQUID createAndTrim' :: Int -> (Ptr Word8 -> IO (Int, Int, a)) -> IO (ByteString, a)
-- LIQUID createAndTrim' l f = do
-- LIQUID     fp <- mallocByteString l
-- LIQUID     withForeignPtr fp $ \p -> do
-- LIQUID         (off, l', res) <- f p
-- LIQUID         if assert (l' <= l) $ l' >= l
-- LIQUID             then return $! (PS fp 0 l, res)
-- LIQUID             else do ps <- create l' $ \p' ->
-- LIQUID                             memcpy p' (p `plusPtr` off) (fromIntegral l')
-- LIQUID                     return $! (ps, res)
-- LIQUID 
-- LIQUID -- | Wrapper of 'mallocForeignPtrBytes' with faster implementation for GHC
-- LIQUID --
mallocByteString :: Int -> IO (ForeignPtr a)
mallocByteString l = do
#ifdef __GLASGOW_HASKELL__
    mallocPlainForeignPtrBytes l
#else
    mallocForeignPtrBytes l
#endif
{-# INLINE mallocByteString #-}

------------------------------------------------------------------------
-- LIQUID 
-- LIQUID -- | Conversion between 'Word8' and 'Char'. Should compile to a no-op.
-- LIQUID w2c :: Word8 -> Char
-- LIQUID #if !defined(__GLASGOW_HASKELL__)
-- LIQUID w2c = chr . fromIntegral
-- LIQUID #else
-- LIQUID w2c = unsafeChr . fromIntegral
-- LIQUID #endif
-- LIQUID {-# INLINE w2c #-}
-- LIQUID 
-- LIQUID -- | Unsafe conversion between 'Char' and 'Word8'. This is a no-op and
-- LIQUID -- silently truncates to 8 bits Chars > '\255'. It is provided as
-- LIQUID -- convenience for ByteString construction.
-- LIQUID c2w :: Char -> Word8
-- LIQUID c2w = fromIntegral . ord
-- LIQUID {-# INLINE c2w #-}
-- LIQUID 
-- LIQUID -- | Selects words corresponding to white-space characters in the Latin-1 range
-- LIQUID -- ordered by frequency. 
-- LIQUID isSpaceWord8 :: Word8 -> Bool
-- LIQUID isSpaceWord8 w =
-- LIQUID     w == 0x20 ||
-- LIQUID     w == 0x0A || -- LF, \n
-- LIQUID     w == 0x09 || -- HT, \t
-- LIQUID     w == 0x0C || -- FF, \f
-- LIQUID     w == 0x0D || -- CR, \r
-- LIQUID     w == 0x0B || -- VT, \v
-- LIQUID     w == 0xA0    -- spotted by QC..
-- LIQUID {-# INLINE isSpaceWord8 #-}
-- LIQUID 
-- LIQUID -- | Selects white-space characters in the Latin-1 range
-- LIQUID isSpaceChar8 :: Char -> Bool
-- LIQUID isSpaceChar8 c =
-- LIQUID     c == ' '     ||
-- LIQUID     c == '\t'    ||
-- LIQUID     c == '\n'    ||
-- LIQUID     c == '\r'    ||
-- LIQUID     c == '\f'    ||
-- LIQUID     c == '\v'    ||
-- LIQUID     c == '\xa0'
-- LIQUID {-# INLINE isSpaceChar8 #-}
-- LIQUID 
-- LIQUID ------------------------------------------------------------------------
-- LIQUID 
-- LIQUID -- | Just like unsafePerformIO, but we inline it. Big performance gains as
-- LIQUID -- it exposes lots of things to further inlining. /Very unsafe/. In
-- LIQUID -- particular, you should do no memory allocation inside an
-- LIQUID -- 'inlinePerformIO' block. On Hugs this is just @unsafePerformIO@.
-- LIQUID --
-- LIQUID {-# INLINE inlinePerformIO #-}
-- LIQUID inlinePerformIO :: IO a -> a
-- LIQUID #if defined(__GLASGOW_HASKELL__)
-- LIQUID inlinePerformIO (IO m) = case m realWorld# of (# _, r #) -> r
-- LIQUID #else
-- LIQUID inlinePerformIO = unsafePerformIO
-- LIQUID #endif
-- LIQUID 
-- LIQUID -- ---------------------------------------------------------------------
-- LIQUID -- 
-- LIQUID -- Standard C functions
-- LIQUID --
-- LIQUID 
-- LIQUID foreign import ccall unsafe "string.h strlen" c_strlen
-- LIQUID     :: CString -> IO CSize
-- LIQUID 
-- LIQUID foreign import ccall unsafe "static stdlib.h &free" c_free_finalizer
-- LIQUID     :: FunPtr (Ptr Word8 -> IO ())
-- LIQUID 
-- LIQUID foreign import ccall unsafe "string.h memchr" c_memchr
-- LIQUID     :: Ptr Word8 -> CInt -> CSize -> IO (Ptr Word8)
-- LIQUID 
-- LIQUID memchr :: Ptr Word8 -> Word8 -> CSize -> IO (Ptr Word8)
-- LIQUID memchr p w s = c_memchr p (fromIntegral w) s
-- LIQUID 
-- LIQUID foreign import ccall unsafe "string.h memcmp" memcmp
-- LIQUID     :: Ptr Word8 -> Ptr Word8 -> CSize -> IO CInt
-- LIQUID 
-- LIQUID foreign import ccall unsafe "string.h memcpy" c_memcpy
-- LIQUID     :: Ptr Word8 -> Ptr Word8 -> CSize -> IO (Ptr Word8)
-- LIQUID 
-- LIQUID memcpy :: Ptr Word8 -> Ptr Word8 -> CSize -> IO ()
-- LIQUID memcpy p q s = c_memcpy p q s >> return ()
-- LIQUID 
-- LIQUID {-
-- LIQUID foreign import ccall unsafe "string.h memmove" c_memmove
-- LIQUID     :: Ptr Word8 -> Ptr Word8 -> CSize -> IO (Ptr Word8)
-- LIQUID 
-- LIQUID memmove :: Ptr Word8 -> Ptr Word8 -> CSize -> IO ()
-- LIQUID memmove p q s = do c_memmove p q s
-- LIQUID                    return ()
-- LIQUID -}
-- LIQUID 
-- LIQUID foreign import ccall unsafe "string.h memset" c_memset
-- LIQUID     :: Ptr Word8 -> CInt -> CSize -> IO (Ptr Word8)
-- LIQUID 
-- LIQUID memset :: Ptr Word8 -> Word8 -> CSize -> IO (Ptr Word8)
-- LIQUID memset p w s = c_memset p (fromIntegral w) s
-- LIQUID 
-- LIQUID -- ---------------------------------------------------------------------
-- LIQUID --
-- LIQUID -- Uses our C code
-- LIQUID --
-- LIQUID 
-- LIQUID foreign import ccall unsafe "static fpstring.h fps_reverse" c_reverse
-- LIQUID     :: Ptr Word8 -> Ptr Word8 -> CULong -> IO ()
-- LIQUID 
-- LIQUID foreign import ccall unsafe "static fpstring.h fps_intersperse" c_intersperse
-- LIQUID     :: Ptr Word8 -> Ptr Word8 -> CULong -> Word8 -> IO ()
-- LIQUID 
-- LIQUID foreign import ccall unsafe "static fpstring.h fps_maximum" c_maximum
-- LIQUID     :: Ptr Word8 -> CULong -> IO Word8
-- LIQUID 
-- LIQUID foreign import ccall unsafe "static fpstring.h fps_minimum" c_minimum
-- LIQUID     :: Ptr Word8 -> CULong -> IO Word8
-- LIQUID 
-- LIQUID foreign import ccall unsafe "static fpstring.h fps_count" c_count
-- LIQUID     :: Ptr Word8 -> CULong -> Word8 -> IO CULong
-- LIQUID 
-- LIQUID -- ---------------------------------------------------------------------
-- LIQUID -- Internal GHC Haskell magic
-- LIQUID 
-- LIQUID #if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 611
-- LIQUID foreign import ccall unsafe "__hscore_memcpy_src_off"
-- LIQUID    memcpy_ptr_baoff :: Ptr a -> RawBuffer -> CInt -> CSize -> IO (Ptr ())
-- LIQUID #endif
