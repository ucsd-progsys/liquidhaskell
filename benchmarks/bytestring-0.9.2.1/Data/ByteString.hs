{-# LANGUAGE CPP #-}
{-# LANGUAGE NamedFieldPuns #-} --LIQUID
-- We cannot actually specify all the language pragmas, see ghc ticket #
-- If we could, these are what they would be:
{- LANGUAGE MagicHash, UnboxedTuples,
            NamedFieldPuns, BangPatterns, RecordWildCards -}
{-# OPTIONS_HADDOCK prune #-}
#if __GLASGOW_HASKELL__ >= 701
{-# LANGUAGE Trustworthy #-}
#endif

-- |
-- Module      : Data.ByteString
-- Copyright   : (c) The University of Glasgow 2001,
--               (c) David Roundy 2003-2005,
--               (c) Simon Marlow 2005
--               (c) Bjorn Bringert 2006
--               (c) Don Stewart 2005-2008
--
--               Array fusion code:
--               (c) 2001,2002 Manuel M T Chakravarty & Gabriele Keller
--               (c) 2006      Manuel M T Chakravarty & Roman Leshchinskiy
--
-- License     : BSD-style
--
-- Maintainer  : dons@cse.unsw.edu.au
-- Stability   : experimental
-- Portability : portable
-- 
-- A time and space-efficient implementation of byte vectors using
-- packed Word8 arrays, suitable for high performance use, both in terms
-- of large data quantities, or high speed requirements. Byte vectors
-- are encoded as strict 'Word8' arrays of bytes, held in a 'ForeignPtr',
-- and can be passed between C and Haskell with little effort.
--
-- This module is intended to be imported @qualified@, to avoid name
-- clashes with "Prelude" functions.  eg.
--
-- > import qualified Data.ByteString as B
--
-- Original GHC implementation by Bryan O\'Sullivan.
-- Rewritten to use 'Data.Array.Unboxed.UArray' by Simon Marlow.
-- Rewritten to support slices and use 'ForeignPtr' by David Roundy.
-- Polished and extended by Don Stewart.
--

module Data.ByteString (

        -- * The @ByteString@ type
        ByteString,             -- abstract, instances: Eq, Ord, Show, Read, Data, Typeable, Monoid

        -- * Introducing and eliminating 'ByteString's
        empty,                  -- :: ByteString
-- LIQUID         singleton,              -- :: Word8   -> ByteString
-- LIQUID         pack,                   -- :: [Word8] -> ByteString
-- LIQUID         unpack,                 -- :: ByteString -> [Word8]
-- LIQUID 
-- LIQUID         -- * Basic interface
-- LIQUID         cons,                   -- :: Word8 -> ByteString -> ByteString
-- LIQUID         snoc,                   -- :: ByteString -> Word8 -> ByteString
-- LIQUID         append,                 -- :: ByteString -> ByteString -> ByteString
-- LIQUID         head,                   -- :: ByteString -> Word8
-- LIQUID         uncons,                 -- :: ByteString -> Maybe (Word8, ByteString)
-- LIQUID         last,                   -- :: ByteString -> Word8
-- LIQUID         tail,                   -- :: ByteString -> ByteString
-- LIQUID         init,                   -- :: ByteString -> ByteString
-- LIQUID         null,                   -- :: ByteString -> Bool
-- LIQUID         length,                 -- :: ByteString -> Int
-- LIQUID 
-- LIQUID         -- * Transforming ByteStrings
-- LIQUID         map,                    -- :: (Word8 -> Word8) -> ByteString -> ByteString
-- LIQUID         reverse,                -- :: ByteString -> ByteString
-- LIQUID         intersperse,            -- :: Word8 -> ByteString -> ByteString
-- LIQUID         intercalate,            -- :: ByteString -> [ByteString] -> ByteString
-- LIQUID         transpose,              -- :: [ByteString] -> [ByteString]
-- LIQUID 
-- LIQUID         -- * Reducing 'ByteString's (folds)
-- LIQUID         foldl,                  -- :: (a -> Word8 -> a) -> a -> ByteString -> a
-- LIQUID         foldl',                 -- :: (a -> Word8 -> a) -> a -> ByteString -> a
-- LIQUID         foldl1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
-- LIQUID         foldl1',                -- :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
-- LIQUID 
-- LIQUID         foldr,                  -- :: (Word8 -> a -> a) -> a -> ByteString -> a
-- LIQUID         foldr',                 -- :: (Word8 -> a -> a) -> a -> ByteString -> a
-- LIQUID         foldr1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
-- LIQUID         foldr1',                -- :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
-- LIQUID 
-- LIQUID         -- ** Special folds
-- LIQUID         concat,                 -- :: [ByteString] -> ByteString
-- LIQUID         concatMap,              -- :: (Word8 -> ByteString) -> ByteString -> ByteString
-- LIQUID         any,                    -- :: (Word8 -> Bool) -> ByteString -> Bool
-- LIQUID         all,                    -- :: (Word8 -> Bool) -> ByteString -> Bool
-- LIQUID         maximum,                -- :: ByteString -> Word8
-- LIQUID         minimum,                -- :: ByteString -> Word8
-- LIQUID 
-- LIQUID         -- * Building ByteStrings
-- LIQUID         -- ** Scans
-- LIQUID         scanl,                  -- :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
-- LIQUID         scanl1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
-- LIQUID         scanr,                  -- :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
-- LIQUID         scanr1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
-- LIQUID 
-- LIQUID         -- ** Accumulating maps
-- LIQUID         mapAccumL,              -- :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
-- LIQUID         mapAccumR,              -- :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
-- LIQUID 
-- LIQUID         -- ** Generating and unfolding ByteStrings
-- LIQUID         replicate,              -- :: Int -> Word8 -> ByteString
-- LIQUID         unfoldr,                -- :: (a -> Maybe (Word8, a)) -> a -> ByteString
-- LIQUID         unfoldrN,               -- :: Int -> (a -> Maybe (Word8, a)) -> a -> (ByteString, Maybe a)
-- LIQUID 
-- LIQUID         -- * Substrings
-- LIQUID 
-- LIQUID         -- ** Breaking strings
-- LIQUID         take,                   -- :: Int -> ByteString -> ByteString
-- LIQUID         drop,                   -- :: Int -> ByteString -> ByteString
-- LIQUID         splitAt,                -- :: Int -> ByteString -> (ByteString, ByteString)
-- LIQUID         takeWhile,              -- :: (Word8 -> Bool) -> ByteString -> ByteString
-- LIQUID         dropWhile,              -- :: (Word8 -> Bool) -> ByteString -> ByteString
-- LIQUID         span,                   -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
-- LIQUID         spanEnd,                -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
-- LIQUID         break,                  -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
-- LIQUID         breakEnd,               -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
-- LIQUID         group,                  -- :: ByteString -> [ByteString]
-- LIQUID         groupBy,                -- :: (Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]
-- LIQUID         inits,                  -- :: ByteString -> [ByteString]
-- LIQUID         tails,                  -- :: ByteString -> [ByteString]
-- LIQUID 
-- LIQUID         -- ** Breaking into many substrings
-- LIQUID         split,                  -- :: Word8 -> ByteString -> [ByteString]
-- LIQUID         splitWith,              -- :: (Word8 -> Bool) -> ByteString -> [ByteString]
-- LIQUID 
-- LIQUID         -- * Predicates
-- LIQUID         isPrefixOf,             -- :: ByteString -> ByteString -> Bool
-- LIQUID         isSuffixOf,             -- :: ByteString -> ByteString -> Bool
-- LIQUID         isInfixOf,              -- :: ByteString -> ByteString -> Bool
-- LIQUID 
-- LIQUID         -- ** Search for arbitrary substrings
-- LIQUID         breakSubstring,         -- :: ByteString -> ByteString -> (ByteString,ByteString)
-- LIQUID         findSubstring,          -- :: ByteString -> ByteString -> Maybe Int
-- LIQUID         findSubstrings,         -- :: ByteString -> ByteString -> [Int]
-- LIQUID 
-- LIQUID         -- * Searching ByteStrings
-- LIQUID 
-- LIQUID         -- ** Searching by equality
-- LIQUID         elem,                   -- :: Word8 -> ByteString -> Bool
-- LIQUID         notElem,                -- :: Word8 -> ByteString -> Bool
-- LIQUID 
-- LIQUID         -- ** Searching with a predicate
-- LIQUID         find,                   -- :: (Word8 -> Bool) -> ByteString -> Maybe Word8
-- LIQUID         filter,                 -- :: (Word8 -> Bool) -> ByteString -> ByteString
-- LIQUID         partition,              -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
-- LIQUID 
-- LIQUID         -- * Indexing ByteStrings
-- LIQUID         index,                  -- :: ByteString -> Int -> Word8
-- LIQUID         elemIndex,              -- :: Word8 -> ByteString -> Maybe Int
-- LIQUID         elemIndices,            -- :: Word8 -> ByteString -> [Int]
-- LIQUID         elemIndexEnd,           -- :: Word8 -> ByteString -> Maybe Int
-- LIQUID         findIndex,              -- :: (Word8 -> Bool) -> ByteString -> Maybe Int
-- LIQUID         findIndices,            -- :: (Word8 -> Bool) -> ByteString -> [Int]
-- LIQUID         count,                  -- :: Word8 -> ByteString -> Int
-- LIQUID 
-- LIQUID         -- * Zipping and unzipping ByteStrings
-- LIQUID         zip,                    -- :: ByteString -> ByteString -> [(Word8,Word8)]
-- LIQUID         zipWith,                -- :: (Word8 -> Word8 -> c) -> ByteString -> ByteString -> [c]
-- LIQUID         unzip,                  -- :: [(Word8,Word8)] -> (ByteString,ByteString)
-- LIQUID 
-- LIQUID         -- * Ordered ByteStrings
-- LIQUID         sort,                   -- :: ByteString -> ByteString
-- LIQUID 
-- LIQUID         -- * Low level conversions
-- LIQUID         -- ** Copying ByteStrings
-- LIQUID         copy,                   -- :: ByteString -> ByteString
-- LIQUID 
-- LIQUID         -- ** Packing 'CString's and pointers
-- LIQUID         packCString,            -- :: CString -> IO ByteString
-- LIQUID         packCStringLen,         -- :: CStringLen -> IO ByteString
-- LIQUID 
-- LIQUID         -- ** Using ByteStrings as 'CString's
-- LIQUID         useAsCString,           -- :: ByteString -> (CString    -> IO a) -> IO a
-- LIQUID         useAsCStringLen,        -- :: ByteString -> (CStringLen -> IO a) -> IO a
-- LIQUID 
-- LIQUID         -- * I\/O with 'ByteString's
-- LIQUID 
-- LIQUID         -- ** Standard input and output
-- LIQUID TODO        getLine,                -- :: IO ByteString
-- LIQUID         getContents,            -- :: IO ByteString
-- LIQUID         putStr,                 -- :: ByteString -> IO ()
-- LIQUID         putStrLn,               -- :: ByteString -> IO ()
-- LIQUID         interact,               -- :: (ByteString -> ByteString) -> IO ()
-- LIQUID 
-- LIQUID         -- ** Files
-- LIQUID         readFile,               -- :: FilePath -> IO ByteString
-- LIQUID         writeFile,              -- :: FilePath -> ByteString -> IO ()
-- LIQUID         appendFile,             -- :: FilePath -> ByteString -> IO ()
-- LIQUID 
-- LIQUID TODO        -- ** I\/O with Handles
-- LIQUID TODO        hGetLine,               -- :: Handle -> IO ByteString
-- LIQUID TODO        hGetContents,           -- :: Handle -> IO ByteString
-- LIQUID TODO        hGet,                   -- :: Handle -> Int -> IO ByteString
-- LIQUID TODO        hGetSome,               -- :: Handle -> Int -> IO ByteString
-- LIQUID TODO        hGetNonBlocking,        -- :: Handle -> Int -> IO ByteString
-- LIQUID TODO        hPut,                   -- :: Handle -> ByteString -> IO ()
-- LIQUID TODO        hPutNonBlocking,        -- :: Handle -> ByteString -> IO ByteString
-- LIQUID TODO        hPutStr,                -- :: Handle -> ByteString -> IO ()
-- LIQUID TODO        hPutStrLn,              -- :: Handle -> ByteString -> IO ()
-- LIQUID TODO
-- LIQUID TODO        breakByte

  ) where

import qualified Prelude as P
import Prelude hiding           (reverse,head,tail,last,init,null
                                ,length,map,lines,foldl,foldr,unlines
                                ,concat,any,take,drop,splitAt,takeWhile
                                ,dropWhile,span,break,elem,filter,maximum
                                ,minimum,all,concatMap,foldl1,foldr1
                                ,scanl,scanl1,scanr,scanr1
                                ,readFile,writeFile,appendFile,replicate
                                ,getContents,getLine,putStr,putStrLn,interact
                                ,zip,zipWith,unzip,notElem)

import Data.ByteString.Internal
import Data.ByteString.Unsafe

import qualified Data.List as List

import Data.Word                (Word8)
import Data.Maybe               (isJust, listToMaybe)

-- Control.Exception.assert not available in yhc or nhc
#ifndef __NHC__
import Control.Exception        (finally, bracket, assert)
#else
import Control.Exception	(bracket, finally)
#endif
import Control.Monad            (when)

import Foreign.C.String         (CString, CStringLen)
import Foreign.C.Types          (CSize, CInt, CULong) -- LIQUID 
import Foreign.ForeignPtr
import Foreign.Marshal.Alloc    (allocaBytes, mallocBytes, reallocBytes, finalizerFree)
import Foreign.Marshal.Array    (allocaArray)
import Foreign.Ptr
import Foreign.Storable         (Storable(..))

-- hGetBuf and hPutBuf not available in yhc or nhc
import System.IO                (stdin,stdout,hClose,hFileSize
                                ,hGetBuf,hPutBuf,openBinaryFile
                                ,IOMode(..))
import System.IO.Error          (mkIOError, illegalOperationErrorType)

import Data.Monoid              (Monoid, mempty, mappend, mconcat)

#if !defined(__GLASGOW_HASKELL__)
import System.IO.Unsafe
import qualified System.Environment
import qualified System.IO      (hGetLine)
import System.IO                (hIsEOF)
#endif

#if defined(__GLASGOW_HASKELL__)

import System.IO                (hGetBufNonBlocking, hPutBufNonBlocking)

-- LIQUID #if MIN_VERSION_base(4,3,0)
-- LIQUID import System.IO                (hGetBufSome)
-- LIQUID #else
import System.IO                (hWaitForInput, hIsEOF)
-- LIQUID #endif

#if __GLASGOW_HASKELL__ >= 611
import Data.IORef
import GHC.IO.Handle.Internals
import GHC.IO.Handle.Types
import GHC.IO.Buffer
import GHC.IO.BufferedIO as Buffered
import GHC.IO                   (stToIO, unsafePerformIO)
import Data.Char                (ord)
import Foreign.Marshal.Utils    (copyBytes)
#else
import System.IO.Error          (isEOFError)
import GHC.IOBase
import GHC.Handle
#endif

-- LIQUID import GHC.Prim                 (Word#, (+#), writeWord8OffAddr#)
import GHC.Base                 (build)
import GHC.Word hiding (Word8)
import GHC.Ptr                  (Ptr(..))
import GHC.ST                   (ST(..))

#endif

-- An alternative to Control.Exception (assert) for nhc98
#ifdef __NHC__

import System.IO (Handle)

#define assert  assertS "__FILE__ : __LINE__"
assertS :: String -> Bool -> a -> a
assertS _ True  = id
assertS s False = error ("assertion failed at "++s)

-- An alternative to hWaitForInput
hWaitForInput :: Handle -> Int -> IO ()
hWaitForInput _ _ = return ()
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
{-@ embed CULong as int @-} -- LIQUID 
{-@ embed CSize  as int @-} -- LIQUID 
{-@ embed CInt   as int @-} -- LIQUID


-- LIQUID instance Eq  ByteString where
-- LIQUID     (==)    = eq
-- LIQUID 
-- LIQUID instance Ord ByteString where
-- LIQUID     compare = compareBytes
-- LIQUID 
-- LIQUID instance Monoid ByteString where
-- LIQUID     mempty  = empty
-- LIQUID     mappend = append
-- LIQUID     mconcat = concat
-- LIQUID 
-- LIQUID -- | /O(n)/ Equality on the 'ByteString' type.
-- LIQUID eq :: ByteString -> ByteString -> Bool
-- LIQUID eq a@(PS p s l) b@(PS p' s' l')
-- LIQUID     | l /= l'            = False    -- short cut on length
-- LIQUID     | p == p' && s == s' = True     -- short cut for the same string
-- LIQUID     | otherwise          = compareBytes a b == EQ
-- LIQUID {-# INLINE eq #-}
-- LIQUID -- ^ still needed

-- | /O(n)/ 'compareBytes' provides an 'Ordering' for 'ByteStrings' supporting slices. 
compareBytes :: ByteString -> ByteString -> Ordering
compareBytes (PS x1 s1 l1) (PS x2 s2 l2)
    | l1 == 0  && l2 == 0               = EQ  -- short cut for empty strings
    | otherwise                         = inlinePerformIO $
        withForeignPtr x1 $ \p1 ->
        withForeignPtr x2 $ \p2 -> do
            i <- memcmp (p1 `plusPtr` s1) (p2 `plusPtr` s2) (fromIntegral $ min l1 l2)
            return $! case i `compare` 0 of
                        EQ  -> l1 `compare` l2
                        x   -> x

{-

-- Pure Haskell version

compareBytes (PS fp1 off1 len1) (PS fp2 off2 len2)
--    | len1 == 0  && len2 == 0                     = EQ  -- short cut for empty strings
--    | fp1 == fp2 && off1 == off2 && len1 == len2  = EQ  -- short cut for the same string
    | otherwise                                   = inlinePerformIO $
    withForeignPtr fp1 $ \p1 ->
        withForeignPtr fp2 $ \p2 ->
            cmp (p1 `plusPtr` off1)
                (p2 `plusPtr` off2) 0 len1 len2

-- XXX todo.
cmp :: Ptr Word8 -> Ptr Word8 -> Int -> Int -> Int-> IO Ordering
cmp p1 p2 n len1 len2
      | n == len1 = if n == len2 then return EQ else return LT
      | n == len2 = return GT
      | otherwise = do
          a <- peekByteOff p1 n :: IO Word8
          b <- peekByteOff p2 n
          case a `compare` b of
                EQ -> cmp p1 p2 (n+1) len1 len2
                LT -> return LT
                GT -> return GT
-}

-- -----------------------------------------------------------------------------
-- Introducing and eliminating 'ByteString's
-- | /O(1)/ The empty 'ByteString'

empty :: ByteString
empty = PS nullForeignPtr 0 0

-- | /O(1)/ Convert a 'Word8' into a 'ByteString'
singleton :: Word8 -> ByteString
singleton c = unsafeCreate 1 $ \p -> poke p c
{-# INLINE [1] singleton #-}

-- Inline [1] for intercalate rule

--
-- XXX The use of unsafePerformIO in allocating functions (unsafeCreate) is critical!
--
-- Otherwise:
--
--  singleton 255 `compare` singleton 127
--
-- is compiled to:
--
--  case mallocByteString 2 of 
--      ForeignPtr f internals -> 
--           case writeWord8OffAddr# f 0 255 of _ -> 
--           case writeWord8OffAddr# f 0 127 of _ ->
--           case eqAddr# f f of 
--                  False -> case compare (GHC.Prim.plusAddr# f 0) 
--                                        (GHC.Prim.plusAddr# f 0)
--
--

-- | /O(n)/ Convert a '[Word8]' into a 'ByteString'. 
--
-- For applications with large numbers of string literals, pack can be a
-- bottleneck. In such cases, consider using packAddress (GHC only).
pack :: [Word8] -> ByteString

-- LIQUID #if !defined(__GLASGOW_HASKELL__)

pack str = unsafeCreate (P.length str) $ \p -> go p str
    where
        go _ []     = return ()
        go p (x:xs) = poke p x >> go (p `plusPtr` 1) xs -- less space than pokeElemOff

-- LIQUID #else /* hack away */
-- LIQUID 
-- LIQUID pack str = unsafeCreate (P.length str) $ \(Ptr p) -> stToIO (go p 0# str)
-- LIQUID     where
-- LIQUID         go _ _ []        = return ()
-- LIQUID         go p i (W8# c:cs) = writeByte p i c >> go p (i +# 1#) cs
-- LIQUID 
-- LIQUID         writeByte p i c = ST $ \s# ->
-- LIQUID             case writeWord8OffAddr# p i c s# of s2# -> (# s2#, () #)
-- LIQUID 
-- LIQUID #endif

-- | /O(n)/ Converts a 'ByteString' to a '[Word8]'.
unpack :: ByteString -> [Word8]

-- LIQUID #if !defined(__GLASGOW_HASKELL__)

unpack (PS _  _ 0) = []
unpack (PS ps s l) = inlinePerformIO $ withForeignPtr ps $ \p ->
        go (p `plusPtr` s) (l - 1) []
    where
        STRICT3(go)
        go p 0 acc = peek p          >>= \e -> return (e : acc)
        go p n acc = peekByteOff p n >>= \e -> go p (n-1) (e : acc)
{-# INLINE unpack #-}

-- LIQUID #else
-- LIQUID 
-- LIQUID unpack ps = build (unpackFoldr ps)
-- LIQUID {-# INLINE unpack #-}
-- LIQUID 
-- LIQUID --
-- LIQUID -- Have unpack fuse with good list consumers
-- LIQUID --
-- LIQUID -- critical this isn't strict in the acc
-- LIQUID -- as it will break in the presence of list fusion. this is a known
-- LIQUID -- issue with seq and build/foldr rewrite rules, which rely on lazy
-- LIQUID -- demanding to avoid bottoms in the list.
-- LIQUID --
-- LIQUID unpackFoldr :: ByteString -> (Word8 -> a -> a) -> a -> a
-- LIQUID unpackFoldr (PS fp off len) f ch = withPtr fp $ \p -> do
-- LIQUID     let loop q n    _   | q `seq` n `seq` False = undefined -- n.b.
-- LIQUID         loop _ (-1) acc = return acc
-- LIQUID         loop q n    acc = do
-- LIQUID            a <- peekByteOff q n
-- LIQUID            loop q (n-1) (a `f` acc)
-- LIQUID     loop (p `plusPtr` off) (len-1) ch
-- LIQUID {-# INLINE [0] unpackFoldr #-}
-- LIQUID 
-- LIQUID unpackList :: ByteString -> [Word8]
-- LIQUID unpackList (PS fp off len) = withPtr fp $ \p -> do
-- LIQUID     let STRICT3(loop)
-- LIQUID         loop _ (-1) acc = return acc
-- LIQUID         loop q n acc = do
-- LIQUID            a <- peekByteOff q n
-- LIQUID            loop q (n-1) (a : acc)
-- LIQUID     loop (p `plusPtr` off) (len-1) []
-- LIQUID 
-- LIQUID {-# RULES
-- LIQUID "ByteString unpack-list" [1]  forall p  .
-- LIQUID     unpackFoldr p (:) [] = unpackList p
-- LIQUID  #-}
-- LIQUID 
-- LIQUID #endif

-- ---------------------------------------------------------------------
-- Basic interface

-- | /O(1)/ Test whether a ByteString is empty.
null :: ByteString -> Bool
null (PS _ _ l) = assert (l >= 0) $ l <= 0
{-# INLINE null #-}

-- ---------------------------------------------------------------------
-- | /O(1)/ 'length' returns the length of a ByteString as an 'Int'.
length :: ByteString -> Int
length (PS _ _ l) = assert (l >= 0) $ l
{-# INLINE length #-}

------------------------------------------------------------------------

-- | /O(n)/ 'cons' is analogous to (:) for lists, but of different
-- complexity, as it requires a memcpy.
cons :: Word8 -> ByteString -> ByteString
cons c (PS x s l) = unsafeCreate (l+1) $ \p -> withForeignPtr x $ \f -> do
        poke p c
        memcpy (p `plusPtr` 1) (f `plusPtr` s) (fromIntegral l)
{-# INLINE cons #-}

-- | /O(n)/ Append a byte to the end of a 'ByteString'
snoc :: ByteString -> Word8 -> ByteString
snoc (PS x s l) c = unsafeCreate (l+1) $ \p -> withForeignPtr x $ \f -> do
        memcpy p (f `plusPtr` s) (fromIntegral l)
        poke (p `plusPtr` l) c
{-# INLINE snoc #-}

-- todo fuse

-- | /O(1)/ Extract the first element of a ByteString, which must be non-empty.
-- An exception will be thrown in the case of an empty ByteString.
head :: ByteString -> Word8
head (PS x s l)
    | l <= 0    = errorEmptyList "head"
    | otherwise = inlinePerformIO $ withForeignPtr x $ \p -> peekByteOff p s
{-# INLINE head #-}

-- | /O(1)/ Extract the elements after the head of a ByteString, which must be non-empty.
-- An exception will be thrown in the case of an empty ByteString.
tail :: ByteString -> ByteString
tail (PS p s l)
    | l <= 0    = errorEmptyList "tail"
    | otherwise = PS p (s+1) (l-1)
{-# INLINE tail #-}

-- | /O(1)/ Extract the head and tail of a ByteString, returning Nothing
-- if it is empty.
uncons :: ByteString -> Maybe (Word8, ByteString)
uncons (PS x s l)
    | l <= 0    = Nothing
    | otherwise = Just (inlinePerformIO $ withForeignPtr x
                                        $ \p -> peekByteOff p s,
                        PS x (s+1) (l-1))
{-# INLINE uncons #-}

-- | /O(1)/ Extract the last element of a ByteString, which must be finite and non-empty.
-- An exception will be thrown in the case of an empty ByteString.
last :: ByteString -> Word8
last ps@(PS x s l)
    | null ps   = errorEmptyList "last"
    | otherwise = inlinePerformIO $ withForeignPtr x $ \p -> peekByteOff p (s+l-1)
{-# INLINE last #-}

-- | /O(1)/ Return all the elements of a 'ByteString' except the last one.
-- An exception will be thrown in the case of an empty ByteString.
init :: ByteString -> ByteString
init ps@(PS p s l)
    | null ps   = errorEmptyList "init"
    | otherwise = PS p s (l-1)
{-# INLINE init #-}

-- | /O(n)/ Append two ByteStrings
append :: ByteString -> ByteString -> ByteString
append xs ys | null xs   = ys
             | null ys   = xs
             | otherwise = concat [xs,ys]
{-# INLINE append #-}

-- ---------------------------------------------------------------------
-- Transformations

-- | /O(n)/ 'map' @f xs@ is the ByteString obtained by applying @f@ to each
-- element of @xs@. This function is subject to array fusion.
map :: (Word8 -> Word8) -> ByteString -> ByteString
map f (PS fp s len) = inlinePerformIO $ withForeignPtr fp $ \a ->
    create len $ map_ 0 (a `plusPtr` s)
  where
    map_ :: Int -> Ptr Word8 -> Ptr Word8 -> IO ()
    STRICT3(map_)
    map_ n p1 p2
       | n >= len = return ()
       | otherwise = do
            x <- peekByteOff p1 n
            pokeByteOff p2 n (f x)
            map_ (n+1) p1 p2
{-# INLINE map #-}

-- | /O(n)/ 'reverse' @xs@ efficiently returns the elements of @xs@ in reverse order.
reverse :: ByteString -> ByteString
reverse (PS x s l) = unsafeCreate l $ \p -> withForeignPtr x $ \f ->
        c_reverse p (f `plusPtr` s) (fromIntegral l)

-- | /O(n)/ The 'intersperse' function takes a 'Word8' and a
-- 'ByteString' and \`intersperses\' that byte between the elements of
-- the 'ByteString'.  It is analogous to the intersperse function on
-- Lists.
intersperse :: Word8 -> ByteString -> ByteString
intersperse c ps@(PS x s l)
    | length ps < 2  = ps
    | otherwise      = unsafeCreate (2*l-1) $ \p -> withForeignPtr x $ \f ->
        c_intersperse p (f `plusPtr` s) (fromIntegral l) c

-- | The 'transpose' function transposes the rows and columns of its
-- 'ByteString' argument.
transpose :: [ByteString] -> [ByteString]
transpose ps = P.map pack (List.transpose (P.map unpack ps))

-- ---------------------------------------------------------------------
-- Reducing 'ByteString's

-- | 'foldl', applied to a binary operator, a starting value (typically
-- the left-identity of the operator), and a ByteString, reduces the
-- ByteString using the binary operator, from left to right.
--
-- This function is subject to array fusion.
--
foldl :: (a -> Word8 -> a) -> a -> ByteString -> a
foldl f v (PS x s l) = inlinePerformIO $ withForeignPtr x $ \ptr ->
        lgo v (ptr `plusPtr` s) (ptr `plusPtr` (s+l))
    where
        STRICT3(lgo)
        lgo z p q | p == q    = return z
                  | otherwise = do c <- peek p
                                   lgo (f z c) (p `plusPtr` 1) q
{-# INLINE foldl #-}

-- | 'foldl\'' is like 'foldl', but strict in the accumulator.
-- However, for ByteStrings, all left folds are strict in the accumulator.
--
foldl' :: (a -> Word8 -> a) -> a -> ByteString -> a
foldl' = foldl
{-# INLINE foldl' #-}

-- | 'foldr', applied to a binary operator, a starting value
-- (typically the right-identity of the operator), and a ByteString,
-- reduces the ByteString using the binary operator, from right to left.
foldr :: (Word8 -> a -> a) -> a -> ByteString -> a
foldr k v (PS x s l) = inlinePerformIO $ withForeignPtr x $ \ptr ->
        go v (ptr `plusPtr` (s+l-1)) (ptr `plusPtr` (s-1))
    where
        STRICT3(go)
        go z p q | p == q    = return z
                 | otherwise = do c  <- peek p
                                  go (c `k` z) (p `plusPtr` (-1)) q -- tail recursive
{-# INLINE foldr #-}

-- | 'foldr\'' is like 'foldr', but strict in the accumulator.
foldr' :: (Word8 -> a -> a) -> a -> ByteString -> a
foldr' k v (PS x s l) = inlinePerformIO $ withForeignPtr x $ \ptr ->
        go v (ptr `plusPtr` (s+l-1)) (ptr `plusPtr` (s-1))
    where
        STRICT3(go)
        go z p q | p == q    = return z
                 | otherwise = do c  <- peek p
                                  go (c `k` z) (p `plusPtr` (-1)) q -- tail recursive
{-# INLINE foldr' #-}

-- | 'foldl1' is a variant of 'foldl' that has no starting value
-- argument, and thus must be applied to non-empty 'ByteStrings'.
-- This function is subject to array fusion. 
-- An exception will be thrown in the case of an empty ByteString.
foldl1 :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldl1 f ps
    | null ps   = errorEmptyList "foldl1"
    | otherwise = foldl f (unsafeHead ps) (unsafeTail ps)
{-# INLINE foldl1 #-}

-- | 'foldl1\'' is like 'foldl1', but strict in the accumulator.
-- An exception will be thrown in the case of an empty ByteString.
foldl1' :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldl1' f ps
    | null ps   = errorEmptyList "foldl1'"
    | otherwise = foldl' f (unsafeHead ps) (unsafeTail ps)
{-# INLINE foldl1' #-}

-- | 'foldr1' is a variant of 'foldr' that has no starting value argument,
-- and thus must be applied to non-empty 'ByteString's
-- An exception will be thrown in the case of an empty ByteString.
foldr1 :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldr1 f ps
    | null ps        = errorEmptyList "foldr1"
    | otherwise      = foldr f (last ps) (init ps)
{-# INLINE foldr1 #-}

-- | 'foldr1\'' is a variant of 'foldr1', but is strict in the
-- accumulator.
foldr1' :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldr1' f ps
    | null ps        = errorEmptyList "foldr1"
    | otherwise      = foldr' f (last ps) (init ps)
{-# INLINE foldr1' #-}

-- ---------------------------------------------------------------------
-- Special folds

-- | /O(n)/ Concatenate a list of ByteStrings.
concat :: [ByteString] -> ByteString
concat []     = empty
concat [ps]   = ps
concat xs     = unsafeCreate len $ \ptr -> go xs ptr
  where len = P.sum . P.map length $ xs
        STRICT2(go)
        go []            _   = return ()
        go (PS p s l:ps) ptr = do
                withForeignPtr p $ \fp -> memcpy ptr (fp `plusPtr` s) (fromIntegral l)
                go ps (ptr `plusPtr` l)

-- | Map a function over a 'ByteString' and concatenate the results
concatMap :: (Word8 -> ByteString) -> ByteString -> ByteString
concatMap f = concat . foldr ((:) . f) []

-- foldr (append . f) empty

-- | /O(n)/ Applied to a predicate and a ByteString, 'any' determines if
-- any element of the 'ByteString' satisfies the predicate.
any :: (Word8 -> Bool) -> ByteString -> Bool
any _ (PS _ _ 0) = False
any f (PS x s l) = inlinePerformIO $ withForeignPtr x $ \ptr ->
        go (ptr `plusPtr` s) (ptr `plusPtr` (s+l))
    where
        STRICT2(go)
        go p q | p == q    = return False
               | otherwise = do c <- peek p
                                if f c then return True
                                       else go (p `plusPtr` 1) q
{-# INLINE any #-}

-- todo fuse

-- | /O(n)/ Applied to a predicate and a 'ByteString', 'all' determines
-- if all elements of the 'ByteString' satisfy the predicate.
all :: (Word8 -> Bool) -> ByteString -> Bool
all _ (PS _ _ 0) = True
all f (PS x s l) = inlinePerformIO $ withForeignPtr x $ \ptr ->
        go (ptr `plusPtr` s) (ptr `plusPtr` (s+l))
    where
        STRICT2(go)
        go p q | p == q     = return True  -- end of list
               | otherwise  = do c <- peek p
                                 if f c
                                    then go (p `plusPtr` 1) q
                                    else return False
{-# INLINE all #-}

------------------------------------------------------------------------

-- | /O(n)/ 'maximum' returns the maximum value from a 'ByteString'
-- This function will fuse.
-- An exception will be thrown in the case of an empty ByteString.
maximum :: ByteString -> Word8
maximum xs@(PS x s l)
    | null xs   = errorEmptyList "maximum"
    | otherwise = inlinePerformIO $ withForeignPtr x $ \p ->
                      c_maximum (p `plusPtr` s) (fromIntegral l)
{-# INLINE maximum #-}

-- | /O(n)/ 'minimum' returns the minimum value from a 'ByteString'
-- This function will fuse.
-- An exception will be thrown in the case of an empty ByteString.
minimum :: ByteString -> Word8
minimum xs@(PS x s l)
    | null xs   = errorEmptyList "minimum"
    | otherwise = inlinePerformIO $ withForeignPtr x $ \p ->
                      c_minimum (p `plusPtr` s) (fromIntegral l)
{-# INLINE minimum #-}

------------------------------------------------------------------------

-- | The 'mapAccumL' function behaves like a combination of 'map' and
-- 'foldl'; it applies a function to each element of a ByteString,
-- passing an accumulating parameter from left to right, and returning a
-- final value of this accumulator together with the new list.
mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumL f acc (PS fp o len) = inlinePerformIO $ withForeignPtr fp $ \a -> do
    gp   <- mallocByteString len
    acc' <- withForeignPtr gp $ \p -> mapAccumL_ acc 0 (a `plusPtr` o) p
    return $! (acc', PS gp 0 len)
  where
    STRICT4(mapAccumL_)
    mapAccumL_ s n p1 p2
       | n >= len = return s
       | otherwise = do
            x <- peekByteOff p1 n
            let (s', y) = f s x
            pokeByteOff p2 n y
            mapAccumL_ s' (n+1) p1 p2
{-# INLINE mapAccumL #-}

-- | The 'mapAccumR' function behaves like a combination of 'map' and
-- 'foldr'; it applies a function to each element of a ByteString,
-- passing an accumulating parameter from right to left, and returning a
-- final value of this accumulator together with the new ByteString.
mapAccumR :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumR f acc (PS fp o len) = inlinePerformIO $ withForeignPtr fp $ \a -> do
    gp   <- mallocByteString len
    acc' <- withForeignPtr gp $ \p -> mapAccumR_ acc (len-1) (a `plusPtr` o) p
    return $! (acc', PS gp 0 len)
  where
    STRICT4(mapAccumR_)
    mapAccumR_ s n p q
       | n <  0    = return s
       | otherwise = do
            x  <- peekByteOff p n
            let (s', y) = f s x
            pokeByteOff q n y
            mapAccumR_ s' (n-1) p q
{-# INLINE mapAccumR #-}

-- ---------------------------------------------------------------------
-- Building ByteStrings

-- | 'scanl' is similar to 'foldl', but returns a list of successive
-- reduced values from the left. This function will fuse.
--
-- > scanl f z [x1, x2, ...] == [z, z `f` x1, (z `f` x1) `f` x2, ...]
--
-- Note that
--
-- > last (scanl f z xs) == foldl f z xs.
--
scanl :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString

scanl f v (PS fp s len) = inlinePerformIO $ withForeignPtr fp $ \a ->
    create (len+1) $ \q -> do
        poke q v
        scanl_ v 0 (a `plusPtr` s) (q `plusPtr` 1)
  where
    STRICT4(scanl_)
    scanl_ z n p q
        | n >= len  = return ()
        | otherwise = do
            x <- peekByteOff p n
            let z' = f z x
            pokeByteOff q n z'
            scanl_ z' (n+1) p q
{-# INLINE scanl #-}

    -- n.b. haskell's List scan returns a list one bigger than the
    -- input, so we need to snoc here to get some extra space, however,
    -- it breaks map/up fusion (i.e. scanl . map no longer fuses)

-- | 'scanl1' is a variant of 'scanl' that has no starting value argument.
-- This function will fuse.
--
-- > scanl1 f [x1, x2, ...] == [x1, x1 `f` x2, ...]
scanl1 :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
scanl1 f ps
    | null ps   = empty
    | otherwise = scanl f (unsafeHead ps) (unsafeTail ps)
{-# INLINE scanl1 #-}

-- | scanr is the right-to-left dual of scanl.
scanr :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
scanr f v (PS fp s len) = inlinePerformIO $ withForeignPtr fp $ \a ->
    create (len+1) $ \q -> do
        poke (q `plusPtr` len) v
        scanr_ v (len-1) (a `plusPtr` s) q
  where
    STRICT4(scanr_)
    scanr_ z n p q
        | n <  0    = return ()
        | otherwise = do
            x <- peekByteOff p n
            let z' = f x z
            pokeByteOff q n z'
            scanr_ z' (n-1) p q
{-# INLINE scanr #-}

-- | 'scanr1' is a variant of 'scanr' that has no starting value argument.
scanr1 :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
scanr1 f ps
    | null ps   = empty
    | otherwise = scanr f (last ps) (init ps) -- todo, unsafe versions
{-# INLINE scanr1 #-}

-- ---------------------------------------------------------------------
-- Unfolds and replicates

-- | /O(n)/ 'replicate' @n x@ is a ByteString of length @n@ with @x@
-- the value of every element. The following holds:
--
-- > replicate w c = unfoldr w (\u -> Just (u,u)) c
--
-- This implemenation uses @memset(3)@
replicate :: Int -> Word8 -> ByteString
replicate w c
    | w <= 0    = empty
    | otherwise = unsafeCreate w $ \ptr ->
                      memset ptr c (fromIntegral w) >> return ()

-- | /O(n)/, where /n/ is the length of the result.  The 'unfoldr' 
-- function is analogous to the List \'unfoldr\'.  'unfoldr' builds a 
-- ByteString from a seed value.  The function takes the element and 
-- returns 'Nothing' if it is done producing the ByteString or returns 
-- 'Just' @(a,b)@, in which case, @a@ is the next byte in the string, 
-- and @b@ is the seed value for further production.
--
-- Examples:
--
-- >    unfoldr (\x -> if x <= 5 then Just (x, x + 1) else Nothing) 0
-- > == pack [0, 1, 2, 3, 4, 5]
--
unfoldr :: (a -> Maybe (Word8, a)) -> a -> ByteString
unfoldr f = concat . unfoldChunk 32 64
  where unfoldChunk n n' x =
          case unfoldrN n f x of
            (s, Nothing) -> s : []
            (s, Just x') -> s : unfoldChunk n' (n+n') x'
{-# INLINE unfoldr #-}

-- | /O(n)/ Like 'unfoldr', 'unfoldrN' builds a ByteString from a seed
-- value.  However, the length of the result is limited by the first
-- argument to 'unfoldrN'.  This function is more efficient than 'unfoldr'
-- when the maximum length of the result is known.
--
-- The following equation relates 'unfoldrN' and 'unfoldr':
--
-- > snd (unfoldrN n f s) == take n (unfoldr f s)
--
unfoldrN :: Int -> (a -> Maybe (Word8, a)) -> a -> (ByteString, Maybe a)
unfoldrN i f x0
    | i < 0     = (empty, Just x0)
    | otherwise = unsafePerformIO $ createAndTrim' i $ \p -> go p x0 0
  where STRICT3(go)
        go p x n =
          case f x of
            Nothing      -> return (0, n, Nothing)
            Just (w,x')
             | n == i    -> return (0, n, Just x)
             | otherwise -> do poke p w
                               go (p `plusPtr` 1) x' (n+1)
{-# INLINE unfoldrN #-}

-- ---------------------------------------------------------------------
-- Substrings

-- | /O(1)/ 'take' @n@, applied to a ByteString @xs@, returns the prefix
-- of @xs@ of length @n@, or @xs@ itself if @n > 'length' xs@.
take :: Int -> ByteString -> ByteString
take n ps@(PS x s l)
    | n <= 0    = empty
    | n >= l    = ps
    | otherwise = PS x s n
{-# INLINE take #-}

-- | /O(1)/ 'drop' @n xs@ returns the suffix of @xs@ after the first @n@
-- elements, or @[]@ if @n > 'length' xs@.
drop  :: Int -> ByteString -> ByteString
drop n ps@(PS x s l)
    | n <= 0    = ps
    | n >= l    = empty
    | otherwise = PS x (s+n) (l-n)
{-# INLINE drop #-}

-- | /O(1)/ 'splitAt' @n xs@ is equivalent to @('take' n xs, 'drop' n xs)@.
splitAt :: Int -> ByteString -> (ByteString, ByteString)
splitAt n ps@(PS x s l)
    | n <= 0    = (empty, ps)
    | n >= l    = (ps, empty)
    | otherwise = (PS x s n, PS x (s+n) (l-n))
{-# INLINE splitAt #-}

-- | 'takeWhile', applied to a predicate @p@ and a ByteString @xs@,
-- returns the longest prefix (possibly empty) of @xs@ of elements that
-- satisfy @p@.
takeWhile :: (Word8 -> Bool) -> ByteString -> ByteString
takeWhile f ps = unsafeTake (findIndexOrEnd (not . f) ps) ps
{-# INLINE takeWhile #-}

-- | 'dropWhile' @p xs@ returns the suffix remaining after 'takeWhile' @p xs@.
dropWhile :: (Word8 -> Bool) -> ByteString -> ByteString
dropWhile f ps = unsafeDrop (findIndexOrEnd (not . f) ps) ps
{-# INLINE dropWhile #-}

-- instead of findIndexOrEnd, we could use memchr here.

-- | 'break' @p@ is equivalent to @'span' ('not' . p)@.
--
-- Under GHC, a rewrite rule will transform break (==) into a
-- call to the specialised breakByte:
--
-- > break ((==) x) = breakByte x
-- > break (==x) = breakByte x
--
break :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
break p ps = case findIndexOrEnd p ps of n -> (unsafeTake n ps, unsafeDrop n ps)
#if __GLASGOW_HASKELL__ 
{-# INLINE [1] break #-}
#endif

{-# RULES
"ByteString specialise break (x==)" forall x.
    break ((==) x) = breakByte x
"ByteString specialise break (==x)" forall x.
    break (==x) = breakByte x
  #-}

-- INTERNAL:

-- | 'breakByte' breaks its ByteString argument at the first occurence
-- of the specified byte. It is more efficient than 'break' as it is
-- implemented with @memchr(3)@. I.e.
-- 
-- > break (=='c') "abcd" == breakByte 'c' "abcd"
--
breakByte :: Word8 -> ByteString -> (ByteString, ByteString)
breakByte c p = case elemIndex c p of
    Nothing -> (p,empty)
    Just n  -> (unsafeTake n p, unsafeDrop n p)
{-# INLINE breakByte #-}

-- | 'breakEnd' behaves like 'break' but from the end of the 'ByteString'
-- 
-- breakEnd p == spanEnd (not.p)
breakEnd :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
breakEnd  p ps = splitAt (findFromEndUntil p ps) ps

-- | 'span' @p xs@ breaks the ByteString into two segments. It is
-- equivalent to @('takeWhile' p xs, 'dropWhile' p xs)@
span :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
span p ps = break (not . p) ps
#if __GLASGOW_HASKELL__
{-# INLINE [1] span #-}
#endif

-- | 'spanByte' breaks its ByteString argument at the first
-- occurence of a byte other than its argument. It is more efficient
-- than 'span (==)'
--
-- > span  (=='c') "abcd" == spanByte 'c' "abcd"
--
spanByte :: Word8 -> ByteString -> (ByteString, ByteString)
spanByte c ps@(PS x s l) = inlinePerformIO $ withForeignPtr x $ \p ->
    go (p `plusPtr` s) 0
  where
    STRICT2(go)
    go p i | i >= l    = return (ps, empty)
           | otherwise = do c' <- peekByteOff p i
                            if c /= c'
                                then return (unsafeTake i ps, unsafeDrop i ps)
                                else go p (i+1)
{-# INLINE spanByte #-}

{-# RULES
"ByteString specialise span (x==)" forall x.
    span ((==) x) = spanByte x
"ByteString specialise span (==x)" forall x.
    span (==x) = spanByte x
  #-}

-- | 'spanEnd' behaves like 'span' but from the end of the 'ByteString'.
-- We have
--
-- > spanEnd (not.isSpace) "x y z" == ("x y ","z")
--
-- and
--
-- > spanEnd (not . isSpace) ps
-- >    == 
-- > let (x,y) = span (not.isSpace) (reverse ps) in (reverse y, reverse x) 
--
spanEnd :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
spanEnd  p ps = splitAt (findFromEndUntil (not.p) ps) ps

-- | /O(n)/ Splits a 'ByteString' into components delimited by
-- separators, where the predicate returns True for a separator element.
-- The resulting components do not contain the separators.  Two adjacent
-- separators result in an empty component in the output.  eg.
--
-- > splitWith (=='a') "aabbaca" == ["","","bb","c",""]
-- > splitWith (=='a') []        == []
--
splitWith :: (Word8 -> Bool) -> ByteString -> [ByteString]

-- LIQUID #if defined(__GLASGOW_HASKELL__)
-- LIQUID splitWith _pred (PS _  _   0) = []
-- LIQUID splitWith pred_ (PS fp off len) = splitWith0 pred# off len fp
-- LIQUID   where pred# c# = pred_ (W8# c#)
-- LIQUID 
-- LIQUID         STRICT4(splitWith0)
-- LIQUID         splitWith0 pred' off' len' fp' = withPtr fp $ \p ->
-- LIQUID             splitLoop pred' p 0 off' len' fp'
-- LIQUID 
-- LIQUID         splitLoop :: (Word# -> Bool)
-- LIQUID                   -> Ptr Word8
-- LIQUID                   -> Int -> Int -> Int
-- LIQUID                   -> ForeignPtr Word8
-- LIQUID                   -> IO [ByteString]
-- LIQUID 
-- LIQUID         splitLoop pred' p idx' off' len' fp'
-- LIQUID             | idx' >= len'  = return [PS fp' off' idx']
-- LIQUID             | otherwise = do
-- LIQUID                 w <- peekElemOff p (off'+idx')
-- LIQUID                 if pred' (case w of W8# w# -> w#)
-- LIQUID                    then return (PS fp' off' idx' :
-- LIQUID                               splitWith0 pred' (off'+idx'+1) (len'-idx'-1) fp')
-- LIQUID                    else splitLoop pred' p (idx'+1) off' len' fp'
-- LIQUID {-# INLINE splitWith #-}
-- LIQUID 
-- LIQUID #else
splitWith _ (PS _ _ 0) = []
splitWith p ps = loop p ps
    where
        STRICT2(loop)
        loop q qs = if null rest then [chunk]
                                 else chunk : loop q (unsafeTail rest)
            where (chunk,rest) = break q qs
-- LIQUID #endif

-- | /O(n)/ Break a 'ByteString' into pieces separated by the byte
-- argument, consuming the delimiter. I.e.
--
-- > split '\n' "a\nb\nd\ne" == ["a","b","d","e"]
-- > split 'a'  "aXaXaXa"    == ["","X","X","X",""]
-- > split 'x'  "x"          == ["",""]
-- 
-- and
--
-- > intercalate [c] . split c == id
-- > split == splitWith . (==)
-- 
-- As for all splitting functions in this library, this function does
-- not copy the substrings, it just constructs new 'ByteStrings' that
-- are slices of the original.
--
split :: Word8 -> ByteString -> [ByteString]
split _ (PS _ _ 0) = []
split w (PS x s l) = loop 0
    where
        STRICT1(loop)
        loop n =
            let q = inlinePerformIO $ withForeignPtr x $ \p ->
                      memchr (p `plusPtr` (s+n))
                             w (fromIntegral (l-n))
            in if q == nullPtr
                then [PS x (s+n) (l-n)]
                else let i = inlinePerformIO $ withForeignPtr x $ \p ->
                               return (q `minusPtr` (p `plusPtr` s))
                      in PS x (s+n) (i-n) : loop (i+1)

{-# INLINE split #-}

{-
-- slower. but stays inside Haskell.
split _ (PS _  _   0) = []
split (W8# w#) (PS fp off len) = splitWith' off len fp
    where
        splitWith' off' len' fp' = withPtr fp $ \p ->
            splitLoop p 0 off' len' fp'

        splitLoop :: Ptr Word8
                  -> Int -> Int -> Int
                  -> ForeignPtr Word8
                  -> IO [ByteString]

        STRICT5(splitLoop)
        splitLoop p idx' off' len' fp'
            | idx' >= len'  = return [PS fp' off' idx']
            | otherwise = do
                (W8# x#) <- peekElemOff p (off'+idx')
                if word2Int# w# ==# word2Int# x#
                   then return (PS fp' off' idx' :
                              splitWith' (off'+idx'+1) (len'-idx'-1) fp')
                   else splitLoop p (idx'+1) off' len' fp'
-}

{-
-- | Like 'splitWith', except that sequences of adjacent separators are
-- treated as a single separator. eg.
-- 
-- > tokens (=='a') "aabbaca" == ["bb","c"]
--
tokens :: (Word8 -> Bool) -> ByteString -> [ByteString]
tokens f = P.filter (not.null) . splitWith f
{-# INLINE tokens #-}
-}

-- | The 'group' function takes a ByteString and returns a list of
-- ByteStrings such that the concatenation of the result is equal to the
-- argument.  Moreover, each sublist in the result contains only equal
-- elements.  For example,
--
-- > group "Mississippi" = ["M","i","ss","i","ss","i","pp","i"]
--
-- It is a special case of 'groupBy', which allows the programmer to
-- supply their own equality test. It is about 40% faster than 
-- /groupBy (==)/
group :: ByteString -> [ByteString]
group xs
    | null xs   = []
    | otherwise = ys : group zs
    where
        (ys, zs) = spanByte (unsafeHead xs) xs

-- | The 'groupBy' function is the non-overloaded version of 'group'.
groupBy :: (Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]
groupBy k xs
    | null xs   = []
    | otherwise = unsafeTake n xs : groupBy k (unsafeDrop n xs)
    where
        n = 1 + findIndexOrEnd (not . k (unsafeHead xs)) (unsafeTail xs)

-- | /O(n)/ The 'intercalate' function takes a 'ByteString' and a list of
-- 'ByteString's and concatenates the list after interspersing the first
-- argument between each element of the list.
intercalate :: ByteString -> [ByteString] -> ByteString
intercalate s = concat . (List.intersperse s)
{-# INLINE [1] intercalate #-}

{-# RULES
"ByteString specialise intercalate c -> intercalateByte" forall c s1 s2 .
    intercalate (singleton c) (s1 : s2 : []) = intercalateWithByte c s1 s2
  #-}

-- | /O(n)/ intercalateWithByte. An efficient way to join to two ByteStrings
-- with a char. Around 4 times faster than the generalised join.
--
intercalateWithByte :: Word8 -> ByteString -> ByteString -> ByteString
intercalateWithByte c f@(PS ffp s l) g@(PS fgp t m) = unsafeCreate len $ \ptr ->
    withForeignPtr ffp $ \fp ->
    withForeignPtr fgp $ \gp -> do
        memcpy ptr (fp `plusPtr` s) (fromIntegral l)
        poke (ptr `plusPtr` l) c
        memcpy (ptr `plusPtr` (l + 1)) (gp `plusPtr` t) (fromIntegral m)
    where
      len = length f + length g + 1
{-# INLINE intercalateWithByte #-}

-- ---------------------------------------------------------------------
-- Indexing ByteStrings

-- | /O(1)/ 'ByteString' index (subscript) operator, starting from 0.
index :: ByteString -> Int -> Word8
index ps n
    | n < 0          = moduleError "index" ("negative index: " ++ show n)
    | n >= length ps = moduleError "index" ("index too large: " ++ show n
                                         ++ ", length = " ++ show (length ps))
    | otherwise      = ps `unsafeIndex` n
{-# INLINE index #-}

-- | /O(n)/ The 'elemIndex' function returns the index of the first
-- element in the given 'ByteString' which is equal to the query
-- element, or 'Nothing' if there is no such element. 
-- This implementation uses memchr(3).
elemIndex :: Word8 -> ByteString -> Maybe Int
elemIndex c (PS x s l) = inlinePerformIO $ withForeignPtr x $ \p -> do
    let p' = p `plusPtr` s
    q <- memchr p' c (fromIntegral l)
    return $! if q == nullPtr then Nothing else Just $! q `minusPtr` p'
{-# INLINE elemIndex #-}

-- | /O(n)/ The 'elemIndexEnd' function returns the last index of the
-- element in the given 'ByteString' which is equal to the query
-- element, or 'Nothing' if there is no such element. The following
-- holds:
--
-- > elemIndexEnd c xs == 
-- > (-) (length xs - 1) `fmap` elemIndex c (reverse xs)
--
elemIndexEnd :: Word8 -> ByteString -> Maybe Int
elemIndexEnd ch (PS x s l) = inlinePerformIO $ withForeignPtr x $ \p ->
    go (p `plusPtr` s) (l-1)
  where
    STRICT2(go)
    go p i | i < 0     = return Nothing
           | otherwise = do ch' <- peekByteOff p i
                            if ch == ch'
                                then return $ Just i
                                else go p (i-1)
{-# INLINE elemIndexEnd #-}

-- | /O(n)/ The 'elemIndices' function extends 'elemIndex', by returning
-- the indices of all elements equal to the query element, in ascending order.
-- This implementation uses memchr(3).
elemIndices :: Word8 -> ByteString -> [Int]
elemIndices w (PS x s l) = loop 0
    where
        STRICT1(loop)
        loop n = let q = inlinePerformIO $ withForeignPtr x $ \p ->
                           memchr (p `plusPtr` (n+s))
                                                w (fromIntegral (l - n))
                 in if q == nullPtr
                        then []
                        else let i = inlinePerformIO $ withForeignPtr x $ \p ->
                                       return (q `minusPtr` (p `plusPtr` s))
                             in i : loop (i+1)
{-# INLINE elemIndices #-}

{-
-- much slower
elemIndices :: Word8 -> ByteString -> [Int]
elemIndices c ps = loop 0 ps
   where STRICT2(loop)
         loop _ ps' | null ps'            = []
         loop n ps' | c == unsafeHead ps' = n : loop (n+1) (unsafeTail ps')
                    | otherwise           = loop (n+1) (unsafeTail ps')
-}

-- | count returns the number of times its argument appears in the ByteString
--
-- > count = length . elemIndices
--
-- But more efficiently than using length on the intermediate list.
count :: Word8 -> ByteString -> Int
count w (PS x s m) = inlinePerformIO $ withForeignPtr x $ \p ->
    fmap fromIntegral $ c_count (p `plusPtr` s) (fromIntegral m) w
{-# INLINE count #-}

{-
--
-- around 30% slower
--
count w (PS x s m) = inlinePerformIO $ withForeignPtr x $ \p ->
     go (p `plusPtr` s) (fromIntegral m) 0
    where
        go :: Ptr Word8 -> CSize -> Int -> IO Int
        STRICT3(go)
        go p l i = do
            q <- memchr p w l
            if q == nullPtr
                then return i
                else do let k = fromIntegral $ q `minusPtr` p
                        go (q `plusPtr` 1) (l-k-1) (i+1)
-}

-- | The 'findIndex' function takes a predicate and a 'ByteString' and
-- returns the index of the first element in the ByteString
-- satisfying the predicate.
findIndex :: (Word8 -> Bool) -> ByteString -> Maybe Int
findIndex k (PS x s l) = inlinePerformIO $ withForeignPtr x $ \f -> go (f `plusPtr` s) 0
  where
    STRICT2(go)
    go ptr n | n >= l    = return Nothing
             | otherwise = do w <- peek ptr
                              if k w
                                then return (Just n)
                                else go (ptr `plusPtr` 1) (n+1)
{-# INLINE findIndex #-}

-- | The 'findIndices' function extends 'findIndex', by returning the
-- indices of all elements satisfying the predicate, in ascending order.
findIndices :: (Word8 -> Bool) -> ByteString -> [Int]
findIndices p ps = loop 0 ps
   where
     STRICT2(loop)
     loop n qs | null qs           = []
               | p (unsafeHead qs) = n : loop (n+1) (unsafeTail qs)
               | otherwise         =     loop (n+1) (unsafeTail qs)

-- ---------------------------------------------------------------------
-- Searching ByteStrings

-- | /O(n)/ 'elem' is the 'ByteString' membership predicate.
elem :: Word8 -> ByteString -> Bool
elem c ps = case elemIndex c ps of Nothing -> False ; _ -> True
{-# INLINE elem #-}

-- | /O(n)/ 'notElem' is the inverse of 'elem'
notElem :: Word8 -> ByteString -> Bool
notElem c ps = not (elem c ps)
{-# INLINE notElem #-}

-- | /O(n)/ 'filter', applied to a predicate and a ByteString,
-- returns a ByteString containing those characters that satisfy the
-- predicate. This function is subject to array fusion.
filter :: (Word8 -> Bool) -> ByteString -> ByteString
filter k ps@(PS x s l)
    | null ps   = ps
    | otherwise = unsafePerformIO $ createAndTrim l $ \p -> withForeignPtr x $ \f -> do
        t <- go (f `plusPtr` s) p (f `plusPtr` (s + l))
        return $! t `minusPtr` p -- actual length
    where
        STRICT3(go)
        go f t end | f == end  = return t
                   | otherwise = do
                        w <- peek f
                        if k w
                            then poke t w >> go (f `plusPtr` 1) (t `plusPtr` 1) end
                            else             go (f `plusPtr` 1) t               end
{-# INLINE filter #-}

{-
--
-- | /O(n)/ A first order equivalent of /filter . (==)/, for the common
-- case of filtering a single byte. It is more efficient to use
-- /filterByte/ in this case.
--
-- > filterByte == filter . (==)
--
-- filterByte is around 10x faster, and uses much less space, than its
-- filter equivalent
--
filterByte :: Word8 -> ByteString -> ByteString
filterByte w ps = replicate (count w ps) w
{-# INLINE filterByte #-}

{-# RULES
"ByteString specialise filter (== x)" forall x.
    filter ((==) x) = filterByte x
"ByteString specialise filter (== x)" forall x.
    filter (== x) = filterByte x
  #-}
-}

-- | /O(n)/ The 'find' function takes a predicate and a ByteString,
-- and returns the first element in matching the predicate, or 'Nothing'
-- if there is no such element.
--
-- > find f p = case findIndex f p of Just n -> Just (p ! n) ; _ -> Nothing
--
find :: (Word8 -> Bool) -> ByteString -> Maybe Word8
find f p = case findIndex f p of
                    Just n -> Just (p `unsafeIndex` n)
                    _      -> Nothing
{-# INLINE find #-}

{-
--
-- fuseable, but we don't want to walk the whole array.
-- 
find k = foldl findEFL Nothing
    where findEFL a@(Just _) _ = a
          findEFL _          c | k c       = Just c
                               | otherwise = Nothing
-}

-- | /O(n)/ The 'partition' function takes a predicate a ByteString and returns
-- the pair of ByteStrings with elements which do and do not satisfy the
-- predicate, respectively; i.e.,
--
-- > partition p bs == (filter p xs, filter (not . p) xs)
--
partition :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
partition p bs = (filter p bs, filter (not . p) bs)
--TODO: use a better implementation

-- ---------------------------------------------------------------------
-- Searching for substrings

-- | /O(n)/ The 'isPrefixOf' function takes two ByteStrings and returns 'True'
-- iff the first is a prefix of the second.
isPrefixOf :: ByteString -> ByteString -> Bool
isPrefixOf (PS x1 s1 l1) (PS x2 s2 l2)
    | l1 == 0   = True
    | l2 < l1   = False
    | otherwise = inlinePerformIO $ withForeignPtr x1 $ \p1 ->
        withForeignPtr x2 $ \p2 -> do
            i <- memcmp (p1 `plusPtr` s1) (p2 `plusPtr` s2) (fromIntegral l1)
            return $! i == 0

-- | /O(n)/ The 'isSuffixOf' function takes two ByteStrings and returns 'True'
-- iff the first is a suffix of the second.
-- 
-- The following holds:
--
-- > isSuffixOf x y == reverse x `isPrefixOf` reverse y
--
-- However, the real implemenation uses memcmp to compare the end of the
-- string only, with no reverse required..
isSuffixOf :: ByteString -> ByteString -> Bool
isSuffixOf (PS x1 s1 l1) (PS x2 s2 l2)
    | l1 == 0   = True
    | l2 < l1   = False
    | otherwise = inlinePerformIO $ withForeignPtr x1 $ \p1 ->
        withForeignPtr x2 $ \p2 -> do
            i <- memcmp (p1 `plusPtr` s1) (p2 `plusPtr` s2 `plusPtr` (l2 - l1)) (fromIntegral l1)
            return $! i == 0

-- | Check whether one string is a substring of another. @isInfixOf
-- p s@ is equivalent to @not (null (findSubstrings p s))@.
isInfixOf :: ByteString -> ByteString -> Bool
isInfixOf p s = isJust (findSubstring p s)

-- | Break a string on a substring, returning a pair of the part of the
-- string prior to the match, and the rest of the string.
--
-- The following relationships hold:
--
-- > break (== c) l == breakSubstring (singleton c) l
--
-- and:
--
-- > findSubstring s l ==
-- >    if null s then Just 0
-- >              else case breakSubstring s l of
-- >                       (x,y) | null y    -> Nothing
-- >                             | otherwise -> Just (length x)
--
-- For example, to tokenise a string, dropping delimiters:
--
-- > tokenise x y = h : if null t then [] else tokenise x (drop (length x) t)
-- >     where (h,t) = breakSubstring x y
--
-- To skip to the first occurence of a string:
-- 
-- > snd (breakSubstring x y) 
--
-- To take the parts of a string before a delimiter:
--
-- > fst (breakSubstring x y) 
--
breakSubstring :: ByteString -- ^ String to search for
               -> ByteString -- ^ String to search in
               -> (ByteString,ByteString) -- ^ Head and tail of string broken at substring

breakSubstring pat src = search 0 src
  where
    STRICT2(search)
    search n s
        | null s             = (src,empty)      -- not found
        | pat `isPrefixOf` s = (take n src,s)
        | otherwise          = search (n+1) (unsafeTail s)

-- | Get the first index of a substring in another string,
--   or 'Nothing' if the string is not found.
--   @findSubstring p s@ is equivalent to @listToMaybe (findSubstrings p s)@.
findSubstring :: ByteString -- ^ String to search for.
              -> ByteString -- ^ String to seach in.
              -> Maybe Int
findSubstring f i = listToMaybe (findSubstrings f i)

{-# DEPRECATED findSubstring "findSubstring is deprecated in favour of breakSubstring." #-}

{-
findSubstring pat str = search 0 str
    where
        STRICT2(search)
        search n s
            = let x = pat `isPrefixOf` s
              in
                if null s
                    then if x then Just n else Nothing
                    else if x then Just n
                              else     search (n+1) (unsafeTail s)
-}

-- | Find the indexes of all (possibly overlapping) occurances of a
-- substring in a string.
--
findSubstrings :: ByteString -- ^ String to search for.
               -> ByteString -- ^ String to seach in.
               -> [Int]
findSubstrings pat str
    | null pat         = [0 .. length str]
    | otherwise        = search 0 str
  where
    STRICT2(search)
    search n s
        | null s             = []
        | pat `isPrefixOf` s = n : search (n+1) (unsafeTail s)
        | otherwise          =     search (n+1) (unsafeTail s)

{-# DEPRECATED findSubstrings "findSubstrings is deprecated in favour of breakSubstring." #-}

{-
{- This function uses the Knuth-Morris-Pratt string matching algorithm.  -}

findSubstrings pat@(PS _ _ m) str@(PS _ _ n) = search 0 0
  where
      patc x = pat `unsafeIndex` x
      strc x = str `unsafeIndex` x

      -- maybe we should make kmpNext a UArray before using it in search?
      kmpNext = listArray (0,m) (-1:kmpNextL pat (-1))
      kmpNextL p _ | null p = []
      kmpNextL p j = let j' = next (unsafeHead p) j + 1
                         ps = unsafeTail p
                         x = if not (null ps) && unsafeHead ps == patc j'
                                then kmpNext Array.! j' else j'
                        in x:kmpNextL ps j'
      search i j = match ++ rest -- i: position in string, j: position in pattern
        where match = if j == m then [(i - j)] else []
              rest = if i == n then [] else search (i+1) (next (strc i) j + 1)
      next c j | j >= 0 && (j == m || c /= patc j) = next c (kmpNext Array.! j)
               | otherwise = j
-}

-- ---------------------------------------------------------------------
-- Zipping

-- | /O(n)/ 'zip' takes two ByteStrings and returns a list of
-- corresponding pairs of bytes. If one input ByteString is short,
-- excess elements of the longer ByteString are discarded. This is
-- equivalent to a pair of 'unpack' operations.
zip :: ByteString -> ByteString -> [(Word8,Word8)]
zip ps qs
    | null ps || null qs = []
    | otherwise = (unsafeHead ps, unsafeHead qs) : zip (unsafeTail ps) (unsafeTail qs)

-- | 'zipWith' generalises 'zip' by zipping with the function given as
-- the first argument, instead of a tupling function.  For example,
-- @'zipWith' (+)@ is applied to two ByteStrings to produce the list of
-- corresponding sums. 
zipWith :: (Word8 -> Word8 -> a) -> ByteString -> ByteString -> [a]
zipWith f ps qs
    | null ps || null qs = []
    | otherwise = f (unsafeHead ps) (unsafeHead qs) : zipWith f (unsafeTail ps) (unsafeTail qs)

--
-- | A specialised version of zipWith for the common case of a
-- simultaneous map over two bytestrings, to build a 3rd. Rewrite rules
-- are used to automatically covert zipWith into zipWith' when a pack is
-- performed on the result of zipWith.
--
zipWith' :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString -> ByteString
zipWith' f (PS fp s l) (PS fq t m) = inlinePerformIO $
    withForeignPtr fp $ \a ->
    withForeignPtr fq $ \b ->
    create len $ zipWith_ 0 (a `plusPtr` s) (b `plusPtr` t)
  where
    zipWith_ :: Int -> Ptr Word8 -> Ptr Word8 -> Ptr Word8 -> IO ()
    STRICT4(zipWith_)
    zipWith_ n p1 p2 r
       | n >= len = return ()
       | otherwise = do
            x <- peekByteOff p1 n
            y <- peekByteOff p2 n
            pokeByteOff r n (f x y)
            zipWith_ (n+1) p1 p2 r

    len = min l m
{-# INLINE zipWith' #-}

{-# RULES
"ByteString specialise zipWith" forall (f :: Word8 -> Word8 -> Word8) p q .
    zipWith f p q = unpack (zipWith' f p q)
  #-}

-- | /O(n)/ 'unzip' transforms a list of pairs of bytes into a pair of
-- ByteStrings. Note that this performs two 'pack' operations.
unzip :: [(Word8,Word8)] -> (ByteString,ByteString)
unzip ls = (pack (P.map fst ls), pack (P.map snd ls))
{-# INLINE unzip #-}

-- ---------------------------------------------------------------------
-- Special lists

-- | /O(n)/ Return all initial segments of the given 'ByteString', shortest first.
inits :: ByteString -> [ByteString]
inits (PS x s l) = [PS x s n | n <- [0..l]]

-- | /O(n)/ Return all final segments of the given 'ByteString', longest first.
tails :: ByteString -> [ByteString]
tails p | null p    = [empty]
        | otherwise = p : tails (unsafeTail p)

-- less efficent spacewise: tails (PS x s l) = [PS x (s+n) (l-n) | n <- [0..l]]

-- ---------------------------------------------------------------------
-- ** Ordered 'ByteString's

-- | /O(n)/ Sort a ByteString efficiently, using counting sort.
sort :: ByteString -> ByteString
sort (PS input s l) = unsafeCreate l $ \p -> allocaArray 256 $ \arr -> do

    _ <- memset (castPtr arr) 0 (256 * fromIntegral (sizeOf (undefined :: CSize)))
    withForeignPtr input (\x -> countOccurrences arr (x `plusPtr` s) l)

    let STRICT2(go)
        go 256 _   = return ()
        go i   ptr = do n <- peekElemOff arr i
                        when (n /= 0) $ memset ptr (fromIntegral i) n >> return ()
                        go (i + 1) (ptr `plusPtr` (fromIntegral n))
    go 0 p
  where
    -- | Count the number of occurrences of each byte.
    -- Used by 'sort'
    --
    countOccurrences :: Ptr CSize -> Ptr Word8 -> Int -> IO ()
    STRICT3(countOccurrences)
    countOccurrences counts str len = go 0
     where
        STRICT1(go)
        go i | i == len    = return ()
             | otherwise = do k <- fromIntegral `fmap` peekElemOff str i
                              x <- peekElemOff counts k
                              pokeElemOff counts k (x + 1)
                              go (i + 1)

{-
sort :: ByteString -> ByteString
sort (PS x s l) = unsafeCreate l $ \p -> withForeignPtr x $ \f -> do
        memcpy p (f `plusPtr` s) l
        c_qsort p l -- inplace
-}

-- The 'sortBy' function is the non-overloaded version of 'sort'.
--
-- Try some linear sorts: radix, counting
-- Or mergesort.
--
-- sortBy :: (Word8 -> Word8 -> Ordering) -> ByteString -> ByteString
-- sortBy f ps = undefined

-- ---------------------------------------------------------------------
-- Low level constructors

-- | /O(n) construction/ Use a @ByteString@ with a function requiring a
-- null-terminated @CString@.  The @CString@ will be freed
-- automatically. This is a memcpy(3).
useAsCString :: ByteString -> (CString -> IO a) -> IO a
useAsCString (PS fp o l) action = do
 allocaBytes (l+1) $ \buf ->
   withForeignPtr fp $ \p -> do
     memcpy buf (p `plusPtr` o) (fromIntegral l)
     pokeByteOff buf l (0::Word8)
     action (castPtr buf)

-- | /O(n) construction/ Use a @ByteString@ with a function requiring a @CStringLen@.
-- As for @useAsCString@ this function makes a copy of the original @ByteString@.
useAsCStringLen :: ByteString -> (CStringLen -> IO a) -> IO a
useAsCStringLen p@(PS _ _ l) f = useAsCString p $ \cstr -> f (cstr,l)

------------------------------------------------------------------------

-- | /O(n)./ Construct a new @ByteString@ from a @CString@. The
-- resulting @ByteString@ is an immutable copy of the original
-- @CString@, and is managed on the Haskell heap. The original
-- @CString@ must be null terminated.
packCString :: CString -> IO ByteString
packCString cstr = do
    len <- c_strlen cstr
    packCStringLen (cstr, fromIntegral len)

-- | /O(n)./ Construct a new @ByteString@ from a @CStringLen@. The
-- resulting @ByteString@ is an immutable copy of the original @CStringLen@.
-- The @ByteString@ is a normal Haskell value and will be managed on the
-- Haskell heap.
packCStringLen :: CStringLen -> IO ByteString
packCStringLen (cstr, len) | len >= 0 = create len $ \p ->
    memcpy p (castPtr cstr) (fromIntegral len)
packCStringLen (_, len) =
    moduleError "packCStringLen" ("negative length: " ++ show len)

------------------------------------------------------------------------

-- | /O(n)/ Make a copy of the 'ByteString' with its own storage. 
-- This is mainly useful to allow the rest of the data pointed
-- to by the 'ByteString' to be garbage collected, for example
-- if a large string has been read in, and only a small part of it 
-- is needed in the rest of the program.
-- 
copy :: ByteString -> ByteString
copy (PS x s l) = unsafeCreate l $ \p -> withForeignPtr x $ \f ->
    memcpy p (f `plusPtr` s) (fromIntegral l)

-- ---------------------------------------------------------------------
-- Line IO

-- | Read a line from stdin.
getLine :: IO ByteString
getLine = hGetLine stdin

-- | Read a line from a handle

hGetLine :: Handle -> IO ByteString

-- LIQUID #if !defined(__GLASGOW_HASKELL__)
-- LIQUID 
-- LIQUID hGetLine h = System.IO.hGetLine h >>= return . pack . P.map c2w
-- LIQUID 
-- LIQUID #elif __GLASGOW_HASKELL__ >= 611

hGetLine h =
  wantReadableHandle_ "Data.ByteString.hGetLine" h $
    \ h_@Handle__{haByteBuffer} -> do
      flushCharReadBuffer h_
      buf <- readIORef haByteBuffer
      if isEmptyBuffer buf
         then fill h_ buf 0 []
         else haveBuf h_ buf 0 []
 where

  fill h_@Handle__{haByteBuffer,haDevice} buf len xss =
    len `seq` do
    (r,buf') <- Buffered.fillReadBuffer haDevice buf
    if r == 0
       then do writeIORef haByteBuffer buf{ bufR=0, bufL=0 }
               if len > 0
                  then mkBigPS len xss
                  else ioe_EOF
       else haveBuf h_ buf' len xss

  haveBuf h_@Handle__{haByteBuffer}
          buf@Buffer{ bufRaw=raw, bufR=w, bufL=r }
          len xss =
    do
        off <- findEOL r w raw
        let new_len = len + off - r
        xs <- mkPS raw r off

      -- if eol == True, then off is the offset of the '\n'
      -- otherwise off == w and the buffer is now empty.
        if off /= w
            then do if (w == off + 1)
                            then writeIORef haByteBuffer buf{ bufL=0, bufR=0 }
                            else writeIORef haByteBuffer buf{ bufL = off + 1 }
                    mkBigPS new_len (xs:xss)
            else do
                 fill h_ buf{ bufL=0, bufR=0 } new_len (xs:xss)

  -- find the end-of-line character, if there is one
  findEOL r w raw
        | r == w = return w
        | otherwise =  do
            c <- readWord8Buf raw r
            if c == fromIntegral (ord '\n')
                then return r -- NB. not r+1: don't include the '\n'
                else findEOL (r+1) w raw

mkPS :: RawBuffer Word8 -> Int -> Int -> IO ByteString
mkPS buf start end =
 create len $ \p ->
   withRawBuffer buf $ \pbuf -> do
   copyBytes p (pbuf `plusPtr` start) len
 where
   len = end - start

-- LIQUID #else
-- LIQUID -- GHC 6.10 and older, pre-Unicode IO library
-- LIQUID 
-- LIQUID hGetLine h = wantReadableHandle "Data.ByteString.hGetLine" h $ \ handle_ -> do
-- LIQUID     case haBufferMode handle_ of
-- LIQUID        NoBuffering -> error "no buffering"
-- LIQUID        _other      -> hGetLineBuffered handle_
-- LIQUID 
-- LIQUID  where
-- LIQUID     hGetLineBuffered handle_ = do
-- LIQUID         let ref = haBuffer handle_
-- LIQUID         buf <- readIORef ref
-- LIQUID         hGetLineBufferedLoop handle_ ref buf 0 []
-- LIQUID 
-- LIQUID     hGetLineBufferedLoop handle_ ref
-- LIQUID             buf@Buffer{ bufRPtr=r, bufWPtr=w, bufBuf=raw } len xss =
-- LIQUID         len `seq` do
-- LIQUID         off <- findEOL r w raw
-- LIQUID         let new_len = len + off - r
-- LIQUID         xs <- mkPS raw r off
-- LIQUID 
-- LIQUID       -- if eol == True, then off is the offset of the '\n'
-- LIQUID       -- otherwise off == w and the buffer is now empty.
-- LIQUID         if off /= w
-- LIQUID             then do if (w == off + 1)
-- LIQUID                             then writeIORef ref buf{ bufRPtr=0, bufWPtr=0 }
-- LIQUID                             else writeIORef ref buf{ bufRPtr = off + 1 }
-- LIQUID                     mkBigPS new_len (xs:xss)
-- LIQUID             else do
-- LIQUID                  maybe_buf <- maybeFillReadBuffer (haFD handle_) True (haIsStream handle_)
-- LIQUID                                     buf{ bufWPtr=0, bufRPtr=0 }
-- LIQUID                  case maybe_buf of
-- LIQUID                     -- Nothing indicates we caught an EOF, and we may have a
-- LIQUID                     -- partial line to return.
-- LIQUID                     Nothing -> do
-- LIQUID                          writeIORef ref buf{ bufRPtr=0, bufWPtr=0 }
-- LIQUID                          if new_len > 0
-- LIQUID                             then mkBigPS new_len (xs:xss)
-- LIQUID                             else ioe_EOF
-- LIQUID                     Just new_buf ->
-- LIQUID                          hGetLineBufferedLoop handle_ ref new_buf new_len (xs:xss)
-- LIQUID 
-- LIQUID     -- find the end-of-line character, if there is one
-- LIQUID     findEOL r w raw
-- LIQUID         | r == w = return w
-- LIQUID         | otherwise =  do
-- LIQUID             (c,r') <- readCharFromBuffer raw r
-- LIQUID             if c == '\n'
-- LIQUID                 then return r -- NB. not r': don't include the '\n'
-- LIQUID                 else findEOL r' w raw
-- LIQUID 
-- LIQUID     maybeFillReadBuffer fd is_line is_stream buf = catch
-- LIQUID         (do buf' <- fillReadBuffer fd is_line is_stream buf
-- LIQUID             return (Just buf'))
-- LIQUID         (\e -> if isEOFError e then return Nothing else ioError e)
-- LIQUID 
-- LIQUID -- TODO, rewrite to use normal memcpy
-- LIQUID mkPS :: RawBuffer -> Int -> Int -> IO ByteString
-- LIQUID mkPS buf start end =
-- LIQUID     let len = end - start
-- LIQUID     in create len $ \p -> do
-- LIQUID         memcpy_ptr_baoff p buf (fromIntegral start) (fromIntegral len)
-- LIQUID         return ()
-- LIQUID 
-- LIQUID #endif
-- LIQUID 
mkBigPS :: Int -> [ByteString] -> IO ByteString
mkBigPS _ [ps] = return ps
mkBigPS _ pss = return $! concat (P.reverse pss)

-- ---------------------------------------------------------------------
-- Block IO

-- | Outputs a 'ByteString' to the specified 'Handle'.
hPut :: Handle -> ByteString -> IO ()
hPut _ (PS _  _ 0) = return ()
hPut h (PS ps s l) = withForeignPtr ps $ \p-> hPutBuf h (p `plusPtr` s) l

-- | Similar to 'hPut' except that it will never block. Instead it returns
-- any tail that did not get written. This tail may be 'empty' in the case that
-- the whole string was written, or the whole original string if nothing was
-- written. Partial writes are also possible.
--
-- Note: on Windows and with Haskell implementation other than GHC, this
-- function does not work correctly; it behaves identically to 'hPut'.
--
-- LIQUID #if defined(__GLASGOW_HASKELL__)
hPutNonBlocking :: Handle -> ByteString -> IO ByteString
hPutNonBlocking h bs@(PS ps s l) = do
  bytesWritten <- withForeignPtr ps $ \p-> hPutBufNonBlocking h (p `plusPtr` s) l
  return $! drop bytesWritten bs
-- LIQUID #else
-- LIQUID hPutNonBlocking :: Handle -> B.ByteString -> IO Int
-- LIQUID hPutNonBlocking h bs = hPut h bs >> return empty
-- LIQUID #endif
-- LIQUID 
-- | A synonym for @hPut@, for compatibility 
hPutStr :: Handle -> ByteString -> IO ()
hPutStr = hPut

-- | Write a ByteString to a handle, appending a newline byte
hPutStrLn :: Handle -> ByteString -> IO ()
hPutStrLn h ps
    | length ps < 1024 = hPut h (ps `snoc` 0x0a)
    | otherwise        = hPut h ps >> hPut h (singleton (0x0a)) -- don't copy

-- | Write a ByteString to stdout
putStr :: ByteString -> IO ()
putStr = hPut stdout

-- | Write a ByteString to stdout, appending a newline byte
putStrLn :: ByteString -> IO ()
putStrLn = hPutStrLn stdout

{-# DEPRECATED hPutStrLn
    "Use Data.ByteString.Char8.hPutStrLn instead. (Functions that rely on ASCII encodings belong in Data.ByteString.Char8)"
  #-}
{-# DEPRECATED putStrLn
    "Use Data.ByteString.Char8.putStrLn instead. (Functions that rely on ASCII encodings belong in Data.ByteString.Char8)"
  #-}

------------------------------------------------------------------------
-- Low level IO

-- | Read a 'ByteString' directly from the specified 'Handle'.  This
-- is far more efficient than reading the characters into a 'String'
-- and then using 'pack'. First argument is the Handle to read from, 
-- and the second is the number of bytes to read. It returns the bytes
-- read, up to n, or 'null' if EOF has been reached.
--
-- 'hGet' is implemented in terms of 'hGetBuf'.
--
-- If the handle is a pipe or socket, and the writing end
-- is closed, 'hGet' will behave as if EOF was reached.
--
hGet :: Handle -> Int -> IO ByteString
hGet h i
    | i >  0    = createAndTrim i $ \p -> hGetBuf h p i
    | i == 0    = return empty
    | otherwise = illegalBufferSize h "hGet" i

-- | hGetNonBlocking is similar to 'hGet', except that it will never block
-- waiting for data to become available, instead it returns only whatever data
-- is available.  If there is no data available to be read, 'hGetNonBlocking'
-- returns 'empty'.
--
-- Note: on Windows and with Haskell implementation other than GHC, this
-- function does not work correctly; it behaves identically to 'hGet'.
--
hGetNonBlocking :: Handle -> Int -> IO ByteString
#if defined(__GLASGOW_HASKELL__)
hGetNonBlocking h i
    | i >  0    = createAndTrim i $ \p -> hGetBufNonBlocking h p i
    | i == 0    = return empty
    | otherwise = illegalBufferSize h "hGetNonBlocking" i
#else
hGetNonBlocking = hGet
#endif

-- | Like 'hGet', except that a shorter 'ByteString' may be returned
-- if there are not enough bytes immediately available to satisfy the
-- whole request.  'hGetSome' only blocks if there is no data
-- available, and EOF has not yet been reached.
--
hGetSome :: Handle -> Int -> IO ByteString
hGetSome hh i
-- LIQUID #if MIN_VERSION_base(4,3,0)
-- LIQUID     | i >  0    = createAndTrim i $ \p -> hGetBufSome hh p i
-- LIQUID #else
    | i >  0    = let
                   loop = do
                     s <- hGetNonBlocking hh i
                     if not (null s)
                        then return s
                        else do eof <- hIsEOF hh
                                if eof then return s
                                       else hWaitForInput hh (-1) >> loop
                                         -- for this to work correctly, the
                                         -- Handle should be in binary mode
                                         -- (see GHC ticket #3808)
                  in loop
-- LIQUID #endif
    | i == 0    = return empty
    | otherwise = illegalBufferSize hh "hGetSome" i

illegalBufferSize :: Handle -> String -> Int -> IO a
illegalBufferSize handle fn sz =
    ioError (mkIOError illegalOperationErrorType msg (Just handle) Nothing)
    --TODO: System.IO uses InvalidArgument here, but it's not exported :-(
    where
      msg = fn ++ ": illegal ByteString size " ++ showsPrec 9 sz []


-- | Read entire handle contents strictly into a 'ByteString'.
--
-- This function reads chunks at a time, doubling the chunksize on each
-- read. The final buffer is then realloced to the appropriate size. For
-- files > half of available memory, this may lead to memory exhaustion.
-- Consider using 'readFile' in this case.
--
-- As with 'hGet', the string representation in the file is assumed to
-- be ISO-8859-1.
--
-- The Handle is closed once the contents have been read,
-- or if an exception is thrown.
--
hGetContents :: Handle -> IO ByteString
hGetContents h = always (hClose h) $ do -- strict, so hClose
    let start_size = 1024
    p <- mallocBytes start_size
    i <- hGetBuf h p start_size
    if i < start_size
        then do p' <- reallocBytes p i
                fp <- newForeignPtr finalizerFree p'
                return $! PS fp 0 i
        else f p start_size
    where
        always = flip finally
        f p s = do
            let s' = 2 * s
            p' <- reallocBytes p s'
            i  <- hGetBuf h (p' `plusPtr` s) s
            if i < s
                then do let i' = s + i
                        p'' <- reallocBytes p' i'
                        fp  <- newForeignPtr finalizerFree p''
                        return $! PS fp 0 i'
                else f p' s'

-- | getContents. Read stdin strictly. Equivalent to hGetContents stdin
-- The 'Handle' is closed after the contents have been read.
--
getContents :: IO ByteString
getContents = hGetContents stdin

-- | The interact function takes a function of type @ByteString -> ByteString@
-- as its argument. The entire input from the standard input device is passed
-- to this function as its argument, and the resulting string is output on the
-- standard output device.
--
interact :: (ByteString -> ByteString) -> IO ()
interact transformer = putStr . transformer =<< getContents

-- | Read an entire file strictly into a 'ByteString'.  This is far more
-- efficient than reading the characters into a 'String' and then using
-- 'pack'.  It also may be more efficient than opening the file and
-- reading it using hGet. Files are read using 'binary mode' on Windows,
-- for 'text mode' use the Char8 version of this function.
--
readFile :: FilePath -> IO ByteString
readFile f = bracket (openBinaryFile f ReadMode) hClose
    (\h -> hFileSize h >>= hGet h . fromIntegral)

-- | Write a 'ByteString' to a file.
writeFile :: FilePath -> ByteString -> IO ()
writeFile f txt = bracket (openBinaryFile f WriteMode) hClose
    (\h -> hPut h txt)

-- | Append a 'ByteString' to a file.
appendFile :: FilePath -> ByteString -> IO ()
appendFile f txt = bracket (openBinaryFile f AppendMode) hClose
    (\h -> hPut h txt)

-- ---------------------------------------------------------------------
-- Internal utilities

-- | 'findIndexOrEnd' is a variant of findIndex, that returns the length
-- of the string if no element is found, rather than Nothing.
findIndexOrEnd :: (Word8 -> Bool) -> ByteString -> Int
findIndexOrEnd k (PS x s l) = inlinePerformIO $ withForeignPtr x $ \f -> go (f `plusPtr` s) 0
  where
    STRICT2(go)
    go ptr n | n >= l    = return l
             | otherwise = do w <- peek ptr
                              if k w
                                then return n
                                else go (ptr `plusPtr` 1) (n+1)
{-# INLINE findIndexOrEnd #-}

-- | Perform an operation with a temporary ByteString
withPtr :: ForeignPtr a -> (Ptr a -> IO b) -> b
withPtr fp io = inlinePerformIO (withForeignPtr fp io)
{-# INLINE withPtr #-}

-- Common up near identical calls to `error' to reduce the number
-- constant strings created when compiled:
errorEmptyList :: String -> a
errorEmptyList fun = moduleError fun "empty ByteString"
{-# NOINLINE errorEmptyList #-}

moduleError :: String -> String -> a
moduleError fun msg = error ("Data.ByteString." ++ fun ++ ':':' ':msg)
{-# NOINLINE moduleError #-}

-- Find from the end of the string using predicate
findFromEndUntil :: (Word8 -> Bool) -> ByteString -> Int
STRICT2(findFromEndUntil)
findFromEndUntil f ps@(PS x s l) =
    if null ps then 0
    else if f (last ps) then l
         else findFromEndUntil f (PS x s (l-1))
