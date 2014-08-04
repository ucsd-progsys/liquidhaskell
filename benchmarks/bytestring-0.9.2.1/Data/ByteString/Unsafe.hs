{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
-- |
-- Module      : Data.ByteString.Unsafe
-- License     : BSD-style
-- Maintainer  : dons@cse.unsw.edu.au, duncan@haskell.org
-- Stability   : experimental
-- Portability : portable
-- 
-- A module containing unsafe 'ByteString' operations. This exposes
-- the 'ByteString' representation and low level construction functions.
-- Modules which extend the 'ByteString' system will need to use this module
-- while ideally most users will be able to make do with the public interface
-- modules.
--
module Data.ByteString.Unsafe (

        -- LIQUID
        liquidCanary1,

        -- * Unchecked access
        unsafeHead,             -- :: ByteString -> Word8
        unsafeTail,             -- :: ByteString -> ByteString
        unsafeIndex,            -- :: ByteString -> Int -> Word8
        unsafeTake,             -- :: Int -> ByteString -> ByteString
        unsafeDrop,             -- :: Int -> ByteString -> ByteString

        -- * Low level interaction with CStrings
        -- ** Using ByteStrings with functions for CStrings
        unsafeUseAsCString,     -- :: ByteString -> (CString -> IO a) -> IO a
        unsafeUseAsCStringLen,  -- :: ByteString -> (CStringLen -> IO a) -> IO a

        -- ** Converting CStrings to ByteStrings
        unsafePackCString,      -- :: CString -> IO ByteString
        unsafePackCStringLen,   -- :: CStringLen -> IO ByteString
        unsafePackMallocCString,-- :: CString -> IO ByteString

#if defined(__GLASGOW_HASKELL__)
        unsafePackAddress,          -- :: Addr# -> IO ByteString
        unsafePackAddressLen,       -- :: Int -> Addr# -> IO ByteString
        unsafePackCStringFinalizer, -- :: Ptr Word8 -> Int -> IO () -> IO ByteString
        unsafeFinalize,             -- :: ByteString -> IO ()
#endif

  ) where

import Data.ByteString.Internal

import Foreign.ForeignPtr       (newForeignPtr_, newForeignPtr, withForeignPtr)
import Foreign.Ptr              (Ptr, plusPtr, castPtr)

import Foreign.Storable         (Storable(..))
import Foreign.C.String         (CString, CStringLen)

-- LIQUID
import Language.Haskell.Liquid.Prelude  (liquidError)
import Language.Haskell.Liquid.Foreign  (mkPtr, cSizeInt)
import Foreign.ForeignPtr       (ForeignPtr)
import Data.Word
import Foreign.C.Types          (CChar(..), CInt(..), CSize(..), CULong(..))
import GHC.Base

#ifndef __NHC__
import Control.Exception        (assert)
#endif

import Data.Word                (Word8)

#if defined(__GLASGOW_HASKELL__)
import qualified Foreign.ForeignPtr as FC (finalizeForeignPtr)
import qualified Foreign.Concurrent as FC (newForeignPtr)

--import Data.Generics            (Data(..), Typeable(..))

import GHC.Prim                 (Addr#)
import GHC.Ptr                  (Ptr(..))
#endif

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


{- liquidCanary1 :: x:Int -> {v: Int | v > x} @-}
liquidCanary1     :: Int -> Int
liquidCanary1 x   = x - 1

-- ---------------------------------------------------------------------
--
-- Extensions to the basic interface
--

-- | A variety of 'head' for non-empty ByteStrings. 'unsafeHead' omits the
-- check for the empty case, so there is an obligation on the programmer
-- to provide a proof that the ByteString is non-empty.
{-@ unsafeHead :: {v:ByteString | (bLength v) > 0} -> Word8 @-}
unsafeHead :: ByteString -> Word8
unsafeHead (PS x s l) = assert (l > 0) $
  inlinePerformIO  $  withForeignPtr x $ \p -> peekByteOff p s
{-# INLINE unsafeHead #-}

-- | A variety of 'tail' for non-empty ByteStrings. 'unsafeTail' omits the
-- check for the empty case. As with 'unsafeHead', the programmer must
-- provide a separate proof that the ByteString is non-empty.
{-@ unsafeTail :: b:{v:ByteString | (bLength v) > 0}
               -> {v:ByteString | (bLength v) = (bLength b) - 1} @-}
unsafeTail :: ByteString -> ByteString
unsafeTail (PS ps s l) = assert (l > 0) $ PS ps (s+1) (l-1)
{-# INLINE unsafeTail #-}

-- | Unsafe 'ByteString' index (subscript) operator, starting from 0, returning a 'Word8'
-- This omits the bounds check, which means there is an accompanying
-- obligation on the programmer to ensure the bounds are checked in some
-- other way.

{-@ unsafeIndex :: b:ByteString
                -> {v:Nat | v < (bLength b)}
                -> Word8 
  @-}
unsafeIndex :: ByteString -> Int -> Word8
unsafeIndex (PS x s l) i = assert (i >= 0 && i < l) $
    inlinePerformIO $ withForeignPtr x $ \p -> peekByteOff p (s+i)
{-# INLINE unsafeIndex #-}

-- | A variety of 'take' which omits the checks on @n@ so there is an
-- obligation on the programmer to provide a proof that @0 <= n <= 'length' xs@.
{-@ unsafeTake :: n:Nat -> b:{v: ByteString | n <= (bLength v)} -> (ByteStringN n) @-}
unsafeTake :: Int -> ByteString -> ByteString
unsafeTake n (PS x s l) = assert (0 <= n && n <= l) $ PS x s n
{-# INLINE unsafeTake #-}

-- | A variety of 'drop' which omits the checks on @n@ so there is an
-- obligation on the programmer to provide a proof that @0 <= n <= 'length' xs@.

{-@ unsafeDrop :: n:Nat
               -> b:{v: ByteString | n <= (bLength v)} 
               -> {v:ByteString | (bLength v) = (bLength b) - n} @-}
unsafeDrop  :: Int -> ByteString -> ByteString
unsafeDrop n (PS x s l) = assert (0 <= n && n <= l) $ PS x (s+n) (l-n)
{-# INLINE unsafeDrop #-}


#if defined(__GLASGOW_HASKELL__)
-- | /O(n)/ Pack a null-terminated sequence of bytes, pointed to by an
-- Addr\# (an arbitrary machine address assumed to point outside the
-- garbage-collected heap) into a @ByteString@. A much faster way to
-- create an Addr\# is with an unboxed string literal, than to pack a
-- boxed string. A unboxed string literal is compiled to a static @char
-- []@ by GHC. Establishing the length of the string requires a call to
-- @strlen(3)@, so the Addr# must point to a null-terminated buffer (as
-- is the case with "string"# literals in GHC). Use 'unsafePackAddress'
-- if you know the length of the string statically.
--
-- An example:
--
-- > literalFS = unsafePackAddress "literal"#
--
-- This function is /unsafe/. If you modify the buffer pointed to by the
-- original Addr# this modification will be reflected in the resulting
-- @ByteString@, breaking referential transparency.
--
{-@ unsafePackAddress :: a:Addr# -> IO {v:ByteString | (bLength v) = (addrLen a)}  @-}
unsafePackAddress :: Addr# -> IO ByteString
unsafePackAddress addr# = do
    p <- newForeignPtr_ cstr
    l <- c_strlen cstr
    return $ PS p 0 ({- LIQUID fromIntegral -} cSizeInt l)
  where
    cstr = {- LIQUID Ptr -} mkPtr addr#
{-# INLINE unsafePackAddress #-}



-- | /O(1)/ 'unsafePackAddressLen' provides constant-time construction of
-- 'ByteStrings' which is ideal for string literals. It packs a
-- null-terminated sequence of bytes into a 'ByteString', given a raw
-- 'Addr\#' to the string, and the length of the string.
--
-- This function is /unsafe/ in two ways:
--
-- * the length argument is assumed to be correct. If the length
-- argument is incorrect, it is possible to overstep the end of the
-- byte array.
--
-- * if the underying Addr# is later modified, this change will be
-- reflected in resulting @ByteString@, breaking referential
-- transparency.
--
-- If in doubt, don't use these functions.
--
{-@ unsafePackAddressLen :: len:Nat -> {v:Addr# | len <= (addrLen v)} -> IO {v: ByteString | ((bLength v) = len)} @-}
unsafePackAddressLen :: Int -> Addr# -> IO ByteString
unsafePackAddressLen len addr# = do
    p <- newForeignPtr_ ({- LIQUID Ptr -} mkPtr addr#)
    return $ PS p 0 len
{-# INLINE unsafePackAddressLen #-}

-- | /O(1)/ Construct a 'ByteString' given a Ptr Word8 to a buffer, a
-- length, and an IO action representing a finalizer. This function is
-- not available on Hugs.
--
-- This function is /unsafe/, it is possible to break referential
-- transparency by modifying the underlying buffer pointed to by the
-- first argument. Any changes to the original buffer will be reflected
-- in the resulting @ByteString@.
--

{-@ unsafePackCStringFinalizer :: p:(PtrV Word8) -> {v:Nat | v <= (plen p)} -> IO () -> IO ByteString  @-}
unsafePackCStringFinalizer :: Ptr Word8 -> Int -> IO () -> IO ByteString
unsafePackCStringFinalizer p l f = do
    fp <- FC.newForeignPtr p f
    return $ PS fp 0 l



-- | Explicitly run the finaliser associated with a 'ByteString'.
-- References to this value after finalisation may generate invalid memory
-- references.
--
-- This function is /unsafe/, as there may be other
-- 'ByteStrings' referring to the same underlying pages. If you use
-- this, you need to have a proof of some kind that all 'ByteString's
-- ever generated from the underlying byte array are no longer live.
--
unsafeFinalize :: ByteString -> IO ()
unsafeFinalize (PS p _ _) = FC.finalizeForeignPtr p

#endif

------------------------------------------------------------------------
-- Packing CStrings into ByteStrings

-- | /O(n)/ Build a @ByteString@ from a @CString@. This value will have /no/
-- finalizer associated to it, and will not be garbage collected by
-- Haskell. The ByteString length is calculated using /strlen(3)/,
-- and thus the complexity is a /O(n)/.
--
-- This function is /unsafe/. If the @CString@ is later modified, this
-- change will be reflected in the resulting @ByteString@, breaking
-- referential transparency.
--

{-@ unsafePackCString :: cstr:{v: CString | 0 <= (plen v)} -> IO {v: ByteString | (bLength v) = (plen cstr)} @-}
unsafePackCString :: CString -> IO ByteString
unsafePackCString cstr = do
    fp <- newForeignPtr_ (castPtr cstr)
    l <- c_strlen cstr
    return $! PS fp 0 ({- LIQUID fromIntegral -} cSizeInt l)

-- | /O(1)/ Build a @ByteString@ from a @CStringLen@. This value will
-- have /no/ finalizer associated with it, and will not be garbage
-- collected by Haskell. This operation has /O(1)/ complexity as we
-- already know the final size, so no /strlen(3)/ is required.
--
-- This funtion is /unsafe/. If the original @CStringLen@ is later
-- modified, this change will be reflected in the resulting @ByteString@,
-- breaking referential transparency.

-- LIQUID: tighten spec to use @len@ as size of output ByteString
{-@ unsafePackCStringLen :: CStringLen -> IO ByteString @-}
unsafePackCStringLen :: CStringLen -> IO ByteString
unsafePackCStringLen (ptr,len) = do
  fp <- newForeignPtr_ (castPtr ptr)
  return $! PS fp 0 ({- fromIntegral -} len)

-- | /O(n)/ Build a @ByteString@ from a malloced @CString@. This value will
-- have a @free(3)@ finalizer associated to it.
--
-- This funtion is /unsafe/. If the original @CStringLen@ is later
-- modified, this change will be reflected in the resulting @ByteString@,
-- breaking referential transparency.
--
-- This function is also unsafe if you call its finalizer twice,
-- which will result in a /double free/ error.
--
{-@ unsafePackMallocCString :: cstr:{v: CString | 0 <= (plen v)} -> IO {v: ByteString | (bLength v) = (plen cstr)} @-}
unsafePackMallocCString :: CString -> IO ByteString
unsafePackMallocCString cstr = do
    fp  <- newForeignPtr c_free_finalizer (castPtr cstr)
    len <- c_strlen cstr
    return $! PS fp 0 ({- LIQUID fromIntegral -} cSizeInt len)

-- ---------------------------------------------------------------------

-- | /O(1) construction/ Use a @ByteString@ with a function requiring a
-- @CString@.
--
-- This function does zero copying, and merely unwraps a @ByteString@ to
-- appear as a @CString@. It is /unsafe/ in two ways:
--
-- * After calling this function the @CString@ shares the underlying
-- byte buffer with the original @ByteString@. Thus modifying the
-- @CString@, either in C, or using poke, will cause the contents of the
-- @ByteString@ to change, breaking referential transparency. Other
-- @ByteStrings@ created by sharing (such as those produced via 'take'
-- or 'drop') will also reflect these changes. Modifying the @CString@
-- will break referential transparency. To avoid this, use
-- @useAsCString@, which makes a copy of the original @ByteString@.
--
-- * @CStrings@ are often passed to functions that require them to be
-- null-terminated. If the original @ByteString@ wasn't null terminated,
-- neither will the @CString@ be. It is the programmers responsibility
-- to guarantee that the @ByteString@ is indeed null terminated. If in
-- doubt, use @useAsCString@.
--
{-@ unsafeUseAsCString :: p:ByteString -> ({v: (PtrV CChar) | (bLength p) <= (plen v) } -> IO a) -> IO a @-}
unsafeUseAsCString :: ByteString -> (CString -> IO a) -> IO a
unsafeUseAsCString (PS ps s _) ac = withForeignPtr ps $ \p -> ac (castPtr p `plusPtr` s)


-- | /O(1) construction/ Use a @ByteString@ with a function requiring a
-- @CStringLen@.
-- 
-- This function does zero copying, and merely unwraps a @ByteString@ to
-- appear as a @CStringLen@. It is /unsafe/:
--
-- * After calling this function the @CStringLen@ shares the underlying
-- byte buffer with the original @ByteString@. Thus modifying the
-- @CStringLen@, either in C, or using poke, will cause the contents of the
-- @ByteString@ to change, breaking referential transparency. Other
-- @ByteStrings@ created by sharing (such as those produced via 'take'
-- or 'drop') will also reflect these changes. Modifying the @CStringLen@
-- will break referential transparency. To avoid this, use
-- @useAsCStringLen@, which makes a copy of the original @ByteString@.
--


{-@ unsafeUseAsCStringLen :: b:ByteString -> ((CStringLenN (bLength b)) -> IO a) -> IO a @-}
unsafeUseAsCStringLen :: ByteString -> (CStringLen -> IO a) -> IO a
unsafeUseAsCStringLen (PS ps s l) f = withForeignPtr ps $ \p -> f (castPtr p `plusPtr` s,l)
