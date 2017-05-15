{-# LANGUAGE BangPatterns, CPP, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |
-- Module      : Data.Text.Foreign
-- Copyright   : (c) 2009, 2010 Bryan O'Sullivan
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : GHC
--
-- Support for using 'Text' data with native code via the Haskell
-- foreign function interface.

module Data.Text.Foreign
    (
    -- * Interoperability with native code
    -- $interop
      I16(..)
    -- * Safe conversion functions
    , fromPtr
    , useAsPtr
    , asForeignPtr
    -- * Unsafe conversion code
    , lengthWord16
    , unsafeCopyToPtr
    -- * Low-level manipulation
    -- $lowlevel
    , dropWord16
    , takeWord16
    ) where

#if defined(ASSERTS)
import Control.Exception (assert)
#endif
#if __GLASGOW_HASKELL__ >= 702
import Control.Monad.ST.Unsafe (unsafeIOToST)
#else
import Control.Monad.ST (unsafeIOToST)
#endif
import Data.Text.Internal (Text(..), empty)
import Data.Text.Unsafe (lengthWord16)
import qualified Data.Text.Array as A
import Data.Word (Word16)
import Foreign.Marshal.Alloc (allocaBytes)
import Foreign.Ptr (Ptr, castPtr, plusPtr)
import Foreign.ForeignPtr (ForeignPtr, mallocForeignPtrArray, withForeignPtr)
import Foreign.Storable (peek, poke)

--LIQUID
import Foreign.Storable (Storable)
import Language.Haskell.Liquid.Prelude


-- $interop
--
-- The 'Text' type is implemented using arrays that are not guaranteed
-- to have a fixed address in the Haskell heap. All communication with
-- native code must thus occur by copying data back and forth.
--
-- The 'Text' type's internal representation is UTF-16, using the
-- platform's native endianness.  This makes copied data suitable for
-- use with native libraries that use a similar representation, such
-- as ICU.  To interoperate with native libraries that use different
-- internal representations, such as UTF-8 or UTF-32, consider using
-- the functions in the 'Data.Text.Encoding' module.

-- | A type representing a number of UTF-16 code units.
--LIQUID newtype I16 = I16 Int
--LIQUID     deriving (Bounded, Enum, Eq, Integral, Num, Ord, --LIQUID Read,
--LIQUID               Real, Show)

--LIQUID FIXME: we don't seem to handle `newtype`s properly, the underlying `Int`
--LIQUID        is still typed as an `I16` in our refinements...
data I16 = I16 Int
    deriving (Eq, Ord)

{-@ data I16 = I16 (i::Nat) @-}
{-@ measure getI16 :: I16 -> Int
    getI16 (I16 n) = n
  @-}

{-@ qualif PtrFree(v:Int, p:Ptr a, l:Int): ((l+l)-(v+v)) <= (plen p) @-}

--LIQUID specializing the type for Word16
{-@ Foreign.ForeignPtr.mallocForeignPtrArray :: (Storable a) => n:Nat -> IO {v:(ForeignPtr a) | (fplen v) = (n + n)} @-}
{-@ qualif FPLenNN(v:ForeignPtr a, n:int): (fplen v) = (n + n) @-}


-- | /O(n)/ Create a new 'Text' from a 'Ptr' 'Word16' by copying the
-- contents of the array.
{-@ fromPtr :: p:(PtrV Word16) -> l:{v:I16 | ((getI16 v)*2) = (plen p)} -> IO Text @-}
fromPtr :: Ptr Word16           -- ^ source array
        -> I16                  -- ^ length of source array (in 'Word16' units)
        -> IO Text
fromPtr _   (I16 0)   = return empty
fromPtr ptr (I16 len) =
--LIQUID #if defined(ASSERTS)
    liquidAssert (len > 0) $
--LIQUID #endif
    return $! Text (liquidAssume (A.aLen arr == len) arr) 0 len
  where
    arr = A.run (A.new len >>= copy)
    copy marr = loop len ptr 0
      where
        {- LIQUID WITNESS -}
        loop (d :: Int) !p !i | i == len = return marr
                              | otherwise = do
          A.unsafeWrite marr i =<< unsafeIOToST (peek p)
          loop (d-1) (p `plusPtr` 2) (i + 1)

-- $lowlevel
--
-- Foreign functions that use UTF-16 internally may return indices in
-- units of 'Word16' instead of characters.  These functions may
-- safely be used with such indices, as they will adjust offsets if
-- necessary to preserve the validity of a Unicode string.

-- | /O(1)/ Return the prefix of the 'Text' of @n@ 'Word16' units in
-- length.
--
-- If @n@ would cause the 'Text' to end inside a surrogate pair, the
-- end of the prefix will be advanced by one additional 'Word16' unit
-- to maintain its validity.
takeWord16 :: I16 -> Text -> Text
takeWord16 (I16 n) t@(Text arr off len)
    | n <= 0               = empty
--LIQUID     | n >= len || m >= len = t
--LIQUID     | otherwise            = Text arr off m
    | n >= len = t
    | otherwise = let w = A.unsafeIndex arr (off+n-1)
                      m | w < 0xDB00 || w > 0xD8FF = n
                        | otherwise                = n+1

                  in if m >= len then t
                     else Text arr off m
--LIQUID   where
--LIQUID     w = A.unsafeIndex arr (off+n-1)
--LIQUID     m | w < 0xDB00 || (liquidAssert False w) > 0xD8FF = n
--LIQUID       | otherwise                = n+1

-- | /O(1)/ Return the suffix of the 'Text', with @n@ 'Word16' units
-- dropped from its beginning.
--
-- If @n@ would cause the 'Text' to begin inside a surrogate pair, the
-- beginning of the suffix will be advanced by one additional 'Word16'
-- unit to maintain its validity.
dropWord16 :: I16 -> Text -> Text
dropWord16 (I16 n) t@(Text arr off len)
    | n <= 0               = t
--LIQUID     | n >= len || m >= len = empty
--LIQUID     | otherwise            = Text arr (off+m) (len-m)
    | n >= len = empty
    | otherwise = let m | w < 0xD800 || w > 0xDBFF = n
                        | otherwise                = n+1
                      w = A.unsafeIndex arr (off+n-1)
                  in if m >= len then empty
                     else Text arr (off+m) (len-m)
--LIQUID   where
--LIQUID     m | w < 0xD800 || w > 0xDBFF = n
--LIQUID       | otherwise                = n+1
--LIQUID     w = A.unsafeIndex arr (off+n-1)

-- | /O(n)/ Copy a 'Text' to an array.  The array is assumed to be big
-- enough to hold the contents of the entire 'Text'.
{-@ unsafeCopyToPtr :: t:Text -> {v:PtrV Word16 | (plen v) >= ((tlen t)*2)}
                    -> IO ()
  @-}
unsafeCopyToPtr :: Text -> Ptr Word16 -> IO ()
unsafeCopyToPtr (Text arr off len) ptr = loop len ptr off
  where
    end = off + len
    {- LIQUID WITNESS -}
    loop (d :: Int) !p !i | i == end  = return ()
                          | otherwise = do
      poke p (A.unsafeIndex arr i)
      loop (d-1) (p `plusPtr` 2) (i + 1)


-- | /O(n)/ Perform an action on a temporary, mutable copy of a
-- 'Text'.  The copy is freed as soon as the action returns.
{-@ useAsPtr :: Text -> (PtrV Word16 -> I16 -> IO a) -> IO a @-}
useAsPtr :: Text -> (Ptr Word16 -> I16 -> IO a) -> IO a
useAsPtr t@(Text _arr _off len) action =
    allocaBytes (len + len) {-LIQUID (len * 2)-} $ \buf -> do
      unsafeCopyToPtr t buf
--LIQUID      action (castPtr buf) (fromIntegral len)
      action (castPtr buf) (I16 $ fromIntegral len)


-- | /O(n)/ Make a mutable copy of a 'Text'.
{-@ asForeignPtr :: Text -> IO (ForeignPtr Word16, I16) @-}
asForeignPtr :: Text -> IO (ForeignPtr Word16, I16)
asForeignPtr t@(Text _arr _off len) = do
  fp <- mallocForeignPtrArray len
  withForeignPtr fp $ unsafeCopyToPtr t
  return (fp, I16 len)











