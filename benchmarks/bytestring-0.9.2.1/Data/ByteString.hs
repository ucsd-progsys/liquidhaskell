{-# OPTIONS_GHC -cpp -fglasgow-exts -fno-warn-orphans #-}

-- #prune

-- |
-- Module      : Data.ByteString
-- Copyright   : (c) The University of Glasgow 2001,
--               (c) David Roundy 2003-2005,
--               (c) Simon Marlow 2005
--               (c) Don Stewart 2005-2006
--               (c) Bjorn Bringert 2006
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
        singleton,              -- :: Word8   -> ByteString
        pack,                   -- :: [Word8] -> ByteString
        unpack,                 -- :: ByteString -> [Word8]

        -- * Basic interface
        cons,                   -- :: Word8 -> ByteString -> ByteString
        snoc,                   -- :: ByteString -> Word8 -> ByteString
        append,                 -- :: ByteString -> ByteString -> ByteString
        head,                   -- :: ByteString -> Word8
        uncons,                 -- :: ByteString -> Maybe (Word8, ByteString)
        last,                   -- :: ByteString -> Word8
        tail,                   -- :: ByteString -> ByteString
        init,                   -- :: ByteString -> ByteString
        null,                   -- :: ByteString -> Bool
        length,                 -- :: ByteString -> Int

        -- * Transforming ByteStrings
        map,                    -- :: (Word8 -> Word8) -> ByteString -> ByteString
        reverse,                -- :: ByteString -> ByteString
        intersperse,            -- :: Word8 -> ByteString -> ByteString
-- LIQUID        intercalate,            -- :: ByteString -> [ByteString] -> ByteString
        transpose,              -- :: [ByteString] -> [ByteString]

        -- * Reducing 'ByteString's (folds)
        foldl,                  -- :: (a -> Word8 -> a) -> a -> ByteString -> a
        foldl',                 -- :: (a -> Word8 -> a) -> a -> ByteString -> a
        foldl1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
        foldl1',                -- :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8

        foldr,                  -- :: (Word8 -> a -> a) -> a -> ByteString -> a
        foldr',                 -- :: (Word8 -> a -> a) -> a -> ByteString -> a
        foldr1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
        foldr1',                -- :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8

        -- ** Special folds
        concat,                 -- :: [ByteString] -> ByteString
        concatMap,              -- :: (Word8 -> ByteString) -> ByteString -> ByteString
        any,                    -- :: (Word8 -> Bool) -> ByteString -> Bool
        all,                    -- :: (Word8 -> Bool) -> ByteString -> Bool
        maximum,                -- :: ByteString -> Word8
        minimum,                -- :: ByteString -> Word8

        -- * Building ByteStrings
        -- ** Scans
        scanl,                  -- :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
        scanl1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
        scanr,                  -- :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
        scanr1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString

        -- ** Accumulating maps
        mapAccumL,              -- :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
        mapAccumR,              -- :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
        mapIndexed,             -- :: (Int -> Word8 -> Word8) -> ByteString -> ByteString
-- LIQUID
-- LIQUID        -- ** Generating and unfolding ByteStrings
-- LIQUID        replicate,              -- :: Int -> Word8 -> ByteString
-- LIQUID        unfoldr,                -- :: (a -> Maybe (Word8, a)) -> a -> ByteString
-- LIQUID        unfoldrN,               -- :: Int -> (a -> Maybe (Word8, a)) -> a -> (ByteString, Maybe a)
-- LIQUID
-- LIQUID        -- * Substrings
-- LIQUID
-- LIQUID        -- ** Breaking strings
        take,                   -- :: Int -> ByteString -> ByteString
        drop,                   -- :: Int -> ByteString -> ByteString
        splitAt,                -- :: Int -> ByteString -> (ByteString, ByteString)
-- LIQUID        takeWhile,              -- :: (Word8 -> Bool) -> ByteString -> ByteString
-- LIQUID        dropWhile,              -- :: (Word8 -> Bool) -> ByteString -> ByteString
-- LIQUID        span,                   -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
-- LIQUID        spanEnd,                -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
-- LIQUID        break,                  -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
-- LIQUID        breakEnd,               -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
-- LIQUID        group,                  -- :: ByteString -> [ByteString]
-- LIQUID        groupBy,                -- :: (Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]
-- LIQUID        inits,                  -- :: ByteString -> [ByteString]
-- LIQUID        tails,                  -- :: ByteString -> [ByteString]
-- LIQUID
-- LIQUID        -- ** Breaking into many substrings
-- LIQUID        split,                  -- :: Word8 -> ByteString -> [ByteString]
-- LIQUID        splitWith,              -- :: (Word8 -> Bool) -> ByteString -> [ByteString]
-- LIQUID
-- LIQUID        -- * Predicates
-- LIQUID        isPrefixOf,             -- :: ByteString -> ByteString -> Bool
-- LIQUID        isSuffixOf,             -- :: ByteString -> ByteString -> Bool
-- LIQUID        isInfixOf,              -- :: ByteString -> ByteString -> Bool
-- LIQUID        isSubstringOf,          -- :: ByteString -> ByteString -> Bool
-- LIQUID
-- LIQUID        -- ** Search for arbitrary substrings
-- LIQUID        findSubstring,          -- :: ByteString -> ByteString -> Maybe Int
-- LIQUID        findSubstrings,         -- :: ByteString -> ByteString -> [Int]
-- LIQUID
-- LIQUID        -- * Searching ByteStrings
-- LIQUID
-- LIQUID        -- ** Searching by equality
-- LIQUID        elem,                   -- :: Word8 -> ByteString -> Bool
-- LIQUID        notElem,                -- :: Word8 -> ByteString -> Bool
-- LIQUID
-- LIQUID        -- ** Searching with a predicate
-- LIQUID        find,                   -- :: (Word8 -> Bool) -> ByteString -> Maybe Word8
-- LIQUID        filter,                 -- :: (Word8 -> Bool) -> ByteString -> ByteString
-- LIQUID        partition,              -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
-- LIQUID
-- LIQUID        -- * Indexing ByteStrings
-- LIQUID        index,                  -- :: ByteString -> Int -> Word8
-- LIQUID        elemIndex,              -- :: Word8 -> ByteString -> Maybe Int
-- LIQUID        elemIndices,            -- :: Word8 -> ByteString -> [Int]
-- LIQUID        elemIndexEnd,           -- :: Word8 -> ByteString -> Maybe Int
-- LIQUID        findIndex,              -- :: (Word8 -> Bool) -> ByteString -> Maybe Int
-- LIQUID        findIndices,            -- :: (Word8 -> Bool) -> ByteString -> [Int]
-- LIQUID        count,                  -- :: Word8 -> ByteString -> Int
-- LIQUID
-- LIQUID        -- * Zipping and unzipping ByteStrings
-- LIQUID        zip,                    -- :: ByteString -> ByteString -> [(Word8,Word8)]
-- LIQUID        zipWith,                -- :: (Word8 -> Word8 -> c) -> ByteString -> ByteString -> [c]
-- LIQUID        unzip,                  -- :: [(Word8,Word8)] -> (ByteString,ByteString)
-- LIQUID
-- LIQUID        -- * Ordered ByteStrings
-- LIQUID        sort,                   -- :: ByteString -> ByteString
-- LIQUID
-- LIQUID        -- * Low level conversions
-- LIQUID        -- ** Copying ByteStrings
-- LIQUID        copy,                   -- :: ByteString -> ByteString
-- LIQUID
-- LIQUID        -- ** Packing 'CString's and pointers
-- LIQUID        packCString,            -- :: CString -> IO ByteString
-- LIQUID        packCStringLen,         -- :: CStringLen -> IO ByteString
-- LIQUID
-- LIQUID        -- ** Using ByteStrings as 'CString's
-- LIQUID        useAsCString,           -- :: ByteString -> (CString    -> IO a) -> IO a
-- LIQUID        useAsCStringLen,        -- :: ByteString -> (CStringLen -> IO a) -> IO a
-- LIQUID
-- LIQUID        -- * I\/O with 'ByteString's
-- LIQUID
-- LIQUID        -- ** Standard input and output
-- LIQUID        getLine,                -- :: IO ByteString
-- LIQUID        getContents,            -- :: IO ByteString
-- LIQUID        putStr,                 -- :: ByteString -> IO ()
-- LIQUID        putStrLn,               -- :: ByteString -> IO ()
-- LIQUID        interact,               -- :: (ByteString -> ByteString) -> IO ()
-- LIQUID
-- LIQUID        -- ** Files
-- LIQUID        readFile,               -- :: FilePath -> IO ByteString
-- LIQUID        writeFile,              -- :: FilePath -> ByteString -> IO ()
-- LIQUID        appendFile,             -- :: FilePath -> ByteString -> IO ()
-- LIQUID--      mmapFile,               -- :: FilePath -> IO ByteString
-- LIQUID
-- LIQUID        -- ** I\/O with Handles
-- LIQUID        hGetLine,               -- :: Handle -> IO ByteString
-- LIQUID        hGetContents,           -- :: Handle -> IO ByteString
-- LIQUID        hGet,                   -- :: Handle -> Int -> IO ByteString
-- LIQUID        hGetNonBlocking,        -- :: Handle -> Int -> IO ByteString
-- LIQUID        hPut,                   -- :: Handle -> ByteString -> IO ()
-- LIQUID        hPutStr,                -- :: Handle -> ByteString -> IO ()
-- LIQUID        hPutStrLn,              -- :: Handle -> ByteString -> IO ()
-- LIQUID
-- LIQUID        -- undocumented deprecated things:
-- LIQUID        join                    -- :: ByteString -> [ByteString] -> ByteString

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
import Data.ByteString.Fusion

import qualified Data.List as List

import Data.Word                (Word8)
import Data.Maybe               (listToMaybe)
import Data.Array               (listArray)
import qualified Data.Array as Array ((!))

-- Control.Exception.bracket not available in yhc or nhc
#ifndef __NHC__
import Control.Exception        (bracket, assert)
import qualified Control.Exception as Exception
#else
import IO			(bracket)
#endif
import Control.Monad            (when)

import Foreign.C.String         (CString, CStringLen)
import Foreign.C.Types          (CSize)
import Foreign.ForeignPtr
import Foreign.Marshal.Alloc    (allocaBytes, mallocBytes, reallocBytes, finalizerFree)
import Foreign.Marshal.Array    (allocaArray)
import Foreign.Ptr
import Foreign.Storable         (Storable(..))

-- hGetBuf and hPutBuf not available in yhc or nhc
import System.IO                (stdin,stdout,hClose,hFileSize
                                ,hGetBuf,hPutBuf,openBinaryFile
                                ,Handle,IOMode(..))

import Data.Monoid              (Monoid, mempty, mappend, mconcat)

#if !defined(__GLASGOW_HASKELL__)
import System.IO.Unsafe
import qualified System.Environment
import qualified System.IO      (hGetLine)
#endif

#if defined(__GLASGOW_HASKELL__)

import System.IO                (hGetBufNonBlocking)
import System.IO.Error          (isEOFError)

import GHC.Handle
import GHC.Prim                 (Word#, (+#), writeWord8OffAddr#)
import GHC.Base                 (build)
import GHC.Word hiding (Word8)
import GHC.Ptr                  (Ptr(..))
import GHC.ST                   (ST(..))
import GHC.IOBase

#endif

-- An alternative to Control.Exception (assert) for nhc98
#ifdef __NHC__
#define assert  assertS "__FILE__ : __LINE__"
assertS :: String -> Bool -> a -> a
assertS _ True  = id
assertS s False = error ("assertion failed at "++s)
#endif

-- LIQUID
import GHC.IO.Buffer
import Language.Haskell.Liquid.Prelude (liquidAssert, intCSize) 
import qualified Data.ByteString.Lazy.Internal 
import qualified Data.ByteString.Fusion
import qualified Data.ByteString.Internal
import qualified Data.ByteString.Unsafe
import qualified Foreign.C.Types

{-@ memcpy_ptr_baoff :: p:(Ptr a) 
                     -> RawBuffer b 
                     -> Int 
                     -> {v:CSize | (OkPLen v p)} -> IO (Ptr ())
  @-}
memcpy_ptr_baoff :: Ptr a -> RawBuffer b -> Int -> CSize -> IO (Ptr ())
memcpy_ptr_baoff = error "LIQUIDCOMPAT"

readCharFromBuffer :: RawBuffer b -> Int -> IO (Char, Int)
readCharFromBuffer x y = error "LIQUIDCOMPAT"

wantReadableHandleLIQUID :: String -> Handle -> (Handle__ -> IO a) -> IO a
wantReadableHandleLIQUID x y f = error $ show $ liquidCanaryFusion 12 -- "LIQUIDCOMPAT"

{-@ qualif Gimme(v:a, n:b, acc:a): (len v) = (n + 1 + (len acc)) @-}
{-@ qualif Zog(v:a, p:a)         : (plen p) <= (plen v)          @-}
{-@ qualif Zog(v:a)              : 0 <= (plen v)                 @-}

{-@ qualif BLens(v:a)            : 0 <= (bLengths v)             @-}
{-@ qualif BLenLE(v:GHC.Ptr.Ptr a, bs:b) : (bLengths bs) <= (plen v)     @-}


{-@ measure bLengths  :: [Data.ByteString.Internal.ByteString] -> Int 
    bLengths ([])   = 0
    bLengths (x:xs) = (bLength x) + (bLengths xs)
  @-}

{-@ lengths :: bs:[ByteString] -> {v:Nat | v = (bLengths bs)} @-}
lengths :: [ByteString] -> Int
lengths []     = 0
lengths (b:bs) = length b + lengths bs



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

instance Eq  ByteString
    where (==)    = eq

instance Ord ByteString
  where compare = compareBytes

-- LIQUID instance Monoid ByteString where
-- LIQUID     mempty  = empty
-- LIQUID     mappend = append
-- LIQUID     mconcat = concat

{-
instance Arbitrary PackedString where
    arbitrary = P.pack `fmap` arbitrary
    coarbitrary s = coarbitrary (P.unpack s)
-}

-- | /O(n)/ Equality on the 'ByteString' type.
{-@ eq :: ByteString -> ByteString -> Bool @-}
eq :: ByteString -> ByteString -> Bool
eq a@(PS p s l) b@(PS p' s' l')
    | l /= l'            = False    -- short cut on length
    | p == p' && s == s' = True     -- short cut for the same string
    | otherwise          = compareBytes a b == EQ
{-# INLINE eq #-}

-- | /O(n)/ 'compareBytes' provides an 'Ordering' for 'ByteStrings' supporting slices. 
compareBytes :: ByteString -> ByteString -> Ordering
compareBytes (PS x1 s1 l1) (PS x2 s2 l2)
    | l1 == 0  && l2 == 0               = EQ  -- short cut for empty strings
    | x1 == x2 && s1 == s2 && l1 == l2  = EQ  -- short cut for the same string
    | otherwise                         = inlinePerformIO $
        withForeignPtr x1 $ \p1 ->
        withForeignPtr x2 $ \p2 -> do
            i <- memcmp (p1 `plusPtr` s1) (p2 `plusPtr` s2) (fromIntegral $ min l1 l2)
            return $! case i `compare` 0 of
                        EQ  -> l1 `compare` l2
                        x   -> x
{-# INLINE compareBytes #-}

 
{-
--
-- About 4x slower over 32M
--
compareBytes :: ByteString -> ByteString -> Ordering
compareBytes (PS fp1 off1 len1) (PS fp2 off2 len2) = inlinePerformIO $
    withForeignPtr fp1 $ \p1 ->
        withForeignPtr fp2 $ \p2 ->
            cmp (p1 `plusPtr` off1)
                (p2 `plusPtr` off2) 0 len1 len2

cmp :: Ptr Word8 -> Ptr Word8 -> Int -> Int -> Int-> IO Ordering
STRICT5(cmp)
cmp p1 p2 n len1 len2
      | n == len1 = if n == len2 then return EQ else return LT
      | n == len2 = return GT
      | otherwise = do
          (a :: Word8) <- peekByteOff p1 n
          (b :: Word8) <- peekByteOff p2 n
          case a `compare` b of
                EQ -> cmp p1 p2 (n+1) len1 len2
                LT -> return LT
                GT -> return GT
{-# INLINE compareBytes #-}
-}

-- -----------------------------------------------------------------------------
-- Introducing and eliminating 'ByteString's

-- | /O(1)/ The empty 'ByteString'
{-@ empty :: {v:ByteString | (bLength v) = 0} @-} 
empty :: ByteString
empty = PS nullForeignPtr 0 0

 
-- | /O(1)/ Convert a 'Word8' into a 'ByteString'

{-@ singleton :: Word8 -> {v:ByteString | (bLength v) = 1} @-}
singleton :: Word8 -> ByteString
singleton c = unsafeCreate 1 $ \p -> poke p c
{-# INLINE [1] singleton #-}

--
-- XXX The unsafePerformIO is critical!
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
{-@ pack :: cs:[Word8] -> {v:ByteString | (bLength v) = (len cs)} @-}
pack :: [Word8] -> ByteString

#if !defined(__GLASGOW_HASKELL__)

pack str = unsafeCreate (P.length str) $ \p -> go p str
    where
        go _ []     = return ()
        go p (x:xs) = poke p x >> go (p `plusPtr` 1) xs -- less space than pokeElemOff

#else /* hack away */

pack str = unsafeCreate (P.length str) $ \(Ptr p) -> stToIO (go p 0# str)
    where
        go _ _ []        = return ()
        go p i (W8# c:cs) = writeByte p i c >> go p (i +# 1#) cs

        writeByte p i c = ST $ \s# ->
            case writeWord8OffAddr# p i c s# of s2# -> (# s2#, () #)

#endif


-- | /O(n)/ Converts a 'ByteString' to a '[Word8]'.
{-@ unpack :: b:ByteString -> {v:[Word8] | (len v) = (bLength b)} @-}
unpack :: ByteString -> [Word8]

#if !defined(__GLASGOW_HASKELL__)
-- LIQUID -- unpack (PS _  _ 0) = []
-- LIQUID -- unpack (PS ps s l) = inlinePerformIO $ withForeignPtr ps $ \p ->
-- LIQUID --         ugo (p `plusPtr` s) (l - 1) []
-- LIQUID -- 
-- LIQUID -- ugo :: ForeignPtr Word8 -> Int -> [Word8] -> IO Word8 
-- LIQUID -- ugo p 0 acc = peek p          >>= \e -> return (e : acc)
-- LIQUID -- ugo p n acc = peekByteOff p n >>= \e -> ugo p (n-1) (e : acc)
unpack (PS _  _ 0) = []
unpack (PS ps s l) = inlinePerformIO $ withForeignPtr ps $ \p ->
        go (p `plusPtr` s) (l - 1) []
    where
        STRICT3(go)
        go p 0 acc = peek p          >>= \e -> return (e : acc)
        go p n acc = peekByteOff p n >>= \e -> go p (n-1) (e : acc)
{-# INLINE unpack #-}

#else

-- unpack ps = build (unpackFoldr ps)

-- LIQUID TODO unpackFoldr :: forall <p :: Int -> a -> Prop>. 
--                   b:ByteString 
--                -> (i:Int -> Word8 -> a<p i> -> a<p (i+1)>)
--                -> (a<p 0>)
--                -> (a<p (bLength b)>)
{-# INLINE unpack #-}

-- LIQUID INLINED : unpack ps = build (unpackFoldr ps) = unpackFoldr ps (:) [] 
-- LIQUID INLINED : so inline `f` with `:` and `ch` with `[]`
unpack ps  = unpackFoldrINLINED ps

unpackFoldrINLINED :: ByteString -> [Word8]
unpackFoldrINLINED (PS fp off len) = withPtr fp $ \p -> do
    let loop q n    _   | q `seq` n `seq` False = undefined -- n.b.
        loop _ (-1) acc = return acc
        loop q n    acc = do
           a <- peekByteOff q n
           loop q (n-1) (a : acc)
    loop (p `plusPtr` off) (len-1) [] 

-- critical this isn't strict in the acc
-- as it will break in the presence of list fusion. this is a known
-- issue with seq and build/foldr rewrite rules, which rely on lazy
-- demanding to avoid bottoms in the list.
--
unpackFoldr :: ByteString -> (Word8 -> a -> a) -> a -> a
unpackFoldr (PS fp off len) f ch = withPtr fp $ \p -> do
    let loop q n    _   | q `seq` n `seq` False = undefined -- n.b.
        loop _ (-1) acc = return acc
        loop q n    acc = do
           a <- peekByteOff q n
           loop q (n-1) (a `f` acc)
    loop (p `plusPtr` off) (len-1) ch
{-# INLINE [0] unpackFoldr #-}

{-@ unpackList :: b:ByteString -> {v:[Word8] | (len v) = (bLength b)} @-}
unpackList :: ByteString -> [Word8]
unpackList (PS fp off len) = withPtr fp $ \p -> do
    let STRICT3(loop)
        loop _ (-1) acc = return acc
        loop q n acc = do
           a <- peekByteOff q n
           loop q (n-1) (a : acc)
    loop (p `plusPtr` off) (len-1) []

{-# RULES
    "FPS unpack-list"  [1]  forall p  . unpackFoldr p (:) [] = unpackList p
 #-}

#endif

-- ---------------------------------------------------------------------
-- Basic interface

-- | /O(1)/ Test whether a ByteString is empty.
{-@ null :: b:ByteString -> {v:Bool | ((Prop v) <=> ((bLength b) = 0))} @-}
null :: ByteString -> Bool
null (PS _ _ l) = assert (l >= 0) $ l <= 0
{-# INLINE null #-}

-- ---------------------------------------------------------------------
-- | /O(1)/ 'length' returns the length of a ByteString as an 'Int'.
{-@ length :: b:ByteString -> {v:Nat | v = (bLength b)} @-}
length :: ByteString -> Int
length (PS _ _ l) = assert (l >= 0) $ l
{-# INLINE length #-}

------------------------------------------------------------------------

-- | /O(n)/ 'cons' is analogous to (:) for lists, but of different
-- complexity, as it requires a memcpy.

{-@ cons :: Word8 -> b:ByteString -> {v:ByteString | (bLength v) = 1 + (bLength b)} @-}
cons :: Word8 -> ByteString -> ByteString
cons c (PS x s l) = unsafeCreate (l+1) $ \p -> withForeignPtr x $ \f -> do
        poke p c
        memcpy (p `plusPtr` 1) (f `plusPtr` s) (fromIntegral l)
{-# INLINE cons #-}

-- | /O(n)/ Append a byte to the end of a 'ByteString'
{-@ snoc :: b:ByteString -> Word8 -> {v:ByteString | (bLength v) = 1 + (bLength b)} @-}
snoc :: ByteString -> Word8 -> ByteString
snoc (PS x s l) c = unsafeCreate (l+1) $ \p -> withForeignPtr x $ \f -> do
        memcpy p (f `plusPtr` s) (fromIntegral l)
        poke (p `plusPtr` l) c
{-# INLINE snoc #-}

-- todo fuse

-- | /O(1)/ Extract the first element of a ByteString, which must be non-empty.
-- An exception will be thrown in the case of an empty ByteString.
{-@ head :: ByteStringNE -> Word8 @-}
head :: ByteString -> Word8
head (PS x s l)
    | l <= 0    = errorEmptyList "head"
    | otherwise = inlinePerformIO $ withForeignPtr x $ \p -> peekByteOff p s
{-# INLINE head #-}

-- | /O(1)/ Extract the elements after the head of a ByteString, which must be non-empty.
-- An exception will be thrown in the case of an empty ByteString.
{-@ tail :: b:ByteStringNE -> {v:ByteString | (bLength v) = (bLength b) - 1} @-}
tail :: ByteString -> ByteString
tail (PS p s l)
    | l <= 0    = errorEmptyList "tail"
    | otherwise = PS p (s+1) (l-1)
{-# INLINE tail #-}

-- | /O(1)/ Extract the head and tail of a ByteString, returning Nothing
-- if it is empty.
{-@ uncons :: b:ByteString -> Maybe (Word8, {v:ByteString | (bLength v) = (bLength b) - 1}) @-}
uncons :: ByteString -> Maybe (Word8, ByteString)
uncons (PS x s l)
    | l <= 0    = Nothing
    | otherwise = Just (inlinePerformIO $ withForeignPtr x
                                        $ \p -> peekByteOff p s,
                        PS x (s+1) (l-1))
{-# INLINE uncons #-}

-- | /O(1)/ Extract the last element of a ByteString, which must be finite and non-empty.
-- An exception will be thrown in the case of an empty ByteString.
{-@ last :: ByteStringNE -> Word8 @-}
last :: ByteString -> Word8
last ps@(PS x s l)
    | null ps   = errorEmptyList "last"
    | otherwise = inlinePerformIO $ withForeignPtr x $ \p -> peekByteOff p (s+l-1)
{-# INLINE last #-}

-- | /O(1)/ Return all the elements of a 'ByteString' except the last one.
-- An exception will be thrown in the case of an empty ByteString.
{-@ init :: b:ByteStringNE -> {v:ByteString | (bLength v) = (bLength b) - 1} @-}
init :: ByteString -> ByteString
init ps@(PS p s l)
    | null ps   = errorEmptyList "init"
    | otherwise = PS p s (l-1)
{-# INLINE init #-}

-- | /O(n)/ Append two ByteStrings
{-@ append :: b1:ByteString -> b2:ByteString 
           -> {v:ByteString | (bLength v) = (bLength b1) + (bLength b2)} 
  @-}
append :: ByteString -> ByteString -> ByteString
append xs ys | null xs   = ys
             | null ys   = xs
             | otherwise = concat [xs,ys]
{-# INLINE append #-}

-- ---------------------------------------------------------------------
-- Transformations

-- | /O(n)/ 'map' @f xs@ is the ByteString obtained by applying @f@ to each
-- element of @xs@. This function is subject to array fusion.
{-@ map :: (Word8 -> Word8) -> b:ByteString -> (ByteStringSZ b) @-}
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

{-@ reverse :: b:ByteString -> (ByteStringSZ b) @-}
reverse :: ByteString -> ByteString
reverse (PS x s l) = unsafeCreate l $ \p -> withForeignPtr x $ \f ->
        c_reverse p (f `plusPtr` s) (fromIntegral l)

-- | /O(n)/ The 'intersperse' function takes a 'Word8' and a
-- 'ByteString' and \`intersperses\' that byte between the elements of
-- the 'ByteString'.  It is analogous to the intersperse function on
-- Lists.
{-@ intersperse :: Word8 -> b:ByteString
                -> {v:ByteString |
                     (((bLength b) >= 2) ? ((bLength v) = (2 * (bLength b)) - 1)
                                         : ((bLength v) = (bLength b))) }
  @-}
intersperse :: Word8 -> ByteString -> ByteString
intersperse c ps@(PS x s l)
    | length ps < 2  = ps
    | otherwise      = unsafeCreate ({- 2*l -} (l + l) - 1) $ \p -> withForeignPtr x $ \f ->
        c_intersperse p (f `plusPtr` s) (fromIntegral l) c

{-
intersperse c = pack . List.intersperse c . unpack
-}

-- | The 'transpose' function transposes the rows and columns of its
-- 'ByteString' argument.
transpose :: [ByteString] -> [ByteString]
transpose ps = P.map pack (List.transpose (P.map unpack ps))

-- ---------------------------------------------------------------------
-- Reducing 'ByteString's

-- | 'foldl', applied to a binary operator, a starting value (typically
-- the left-identity of the operator), and a ByteString, reduces the
-- ByteString using the binary operator, from left to right.
-- This function is subject to array fusion.

{-@ foldl :: (a -> Word8 -> a) -> a -> ByteString -> a @-}
foldl :: (a -> Word8 -> a) -> a -> ByteString -> a
foldl f v (PS x s l) = inlinePerformIO $ withForeignPtr x $ \ptr ->
        lgo v (ptr `plusPtr` s) (ptr `plusPtr` (s+l))
    where
        STRICT3(lgo)
        lgo z p q | p == q    = return z
                  | otherwise = do let p' = liquid_thm_ptr_cmp p q 
                                   c <- peek p'
                                   lgo (f z c) (p' `plusPtr` 1) q
{-# INLINE foldl #-}

-- LIQUID: This will go away when we properly embed Ptr a as int -- only in
-- fixpoint to avoid the Sort mismatch hassles. 
{-@ liquid_thm_ptr_cmp :: p:PtrV a 
                       -> q:{v:(PtrV a) | ((plen v) <= (plen p) && v != p && (pbase v) = (pbase p))} 
                       -> {v: (PtrV a)  | ((v = p) && ((plen q) < (plen p))) } 
  @-}
liquid_thm_ptr_cmp :: Ptr a -> Ptr a -> Ptr a
liquid_thm_ptr_cmp p q = undefined -- p -- LIQUID : make this undefined to suppress WARNING


-- | 'foldl\'' is like 'foldl', but strict in the accumulator.
-- Though actually foldl is also strict in the accumulator.
{-@ foldl' :: (a -> Word8 -> a) -> a -> ByteString -> a @-}
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
                 | otherwise = do let p' = liquid_thm_ptr_cmp' p q 
                                  c  <- peek p'
                                  let n  = 0 - 1  
                                  go (c `k` z) (p' `plusPtr` n) q -- tail recursive
        -- LIQUID go z p q | p == q    = return z
        -- LIQUID          | otherwise = do c  <- peek p
        -- LIQUID                           go (c `k` z) (p `plusPtr` (-1)) q -- tail recursive
{-# INLINE foldr #-}

{-@ liquid_thm_ptr_cmp' :: p:PtrV a 
                        -> q:{v:(PtrV a) | ((plen v) >= (plen p) && v != p && (pbase v) = (pbase p))} 
                        -> {v: (PtrV a)  | ((v = p) && ((plen v) > 0) && ((plen q) > (plen p))) } 
  @-}
liquid_thm_ptr_cmp' :: Ptr a -> Ptr a -> Ptr a
liquid_thm_ptr_cmp' p q = undefined 

-- | 'foldr\'' is like 'foldr', but strict in the accumulator.
foldr' :: (Word8 -> a -> a) -> a -> ByteString -> a
foldr' k v (PS x s l) = inlinePerformIO $ withForeignPtr x $ \ptr ->
        go v (ptr `plusPtr` (s+l-1)) (ptr `plusPtr` (s-1))
    where
        STRICT3(go)
        go z p q | p == q    = return z
                 | otherwise = do let p' = liquid_thm_ptr_cmp' p q 
                                  c  <- peek p'
                                  let n  = 0 - 1  
                                  go (c `k` z) (p' `plusPtr` n) q -- tail recursive
        -- LIQUID go z p q | p == q    = return z
        -- LIQUID          | otherwise = do c  <- peek p
        -- LIQUID                           go (c `k` z) (p `plusPtr` (-1)) q -- tail recursive
{-# INLINE foldr' #-}

-- | 'foldl1' is a variant of 'foldl' that has no starting value
-- argument, and thus must be applied to non-empty 'ByteStrings'.
-- This function is subject to array fusion. 
-- An exception will be thrown in the case of an empty ByteString.
{-@ foldl1 :: (Word8 -> Word8 -> Word8) -> ByteStringNE -> Word8 @-}
foldl1 :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldl1 f ps
    | null ps   = errorEmptyList "foldl1"
    | otherwise = foldl f (unsafeHead ps) (unsafeTail ps)
{-# INLINE foldl1 #-}

-- | 'foldl1\'' is like 'foldl1', but strict in the accumulator.
-- An exception will be thrown in the case of an empty ByteString.
{-@ foldl1' :: (Word8 -> Word8 -> Word8) -> ByteStringNE -> Word8 @-}
foldl1' :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldl1' f ps
    | null ps   = errorEmptyList "foldl1'"
    | otherwise = foldl' f (unsafeHead ps) (unsafeTail ps)
{-# INLINE foldl1' #-}

-- | 'foldr1' is a variant of 'foldr' that has no starting value argument,
-- and thus must be applied to non-empty 'ByteString's
-- An exception will be thrown in the case of an empty ByteString.

{-@ foldr1 :: (Word8 -> Word8 -> Word8) -> ByteStringNE -> Word8 @-}
foldr1 :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldr1 f ps
    | null ps        = errorEmptyList "foldr1"
    | otherwise      = foldr f (last ps) (init ps)
{-# INLINE foldr1 #-}

-- | 'foldr1\'' is a variant of 'foldr1', but is strict in the
-- accumulator.
{-@ foldr1' :: (Word8 -> Word8 -> Word8) -> ByteStringNE -> Word8 @-}
foldr1' :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldr1' f ps
    | null ps        = errorEmptyList "foldr1"
    | otherwise      = foldr' f (last ps) (init ps)
{-# INLINE foldr1' #-}

-- ---------------------------------------------------------------------
-- Special folds

-- | /O(n)/ Concatenate a list of ByteStrings.
{-@ concat :: bs:[ByteString] -> {v:ByteString | (bLength v) = (bLengths bs)} @-}
concat :: [ByteString] -> ByteString
concat []     = empty
concat [ps]   = ps
concat xs     = unsafeCreate len $ \ptr -> go xs ptr
  where len = {- LIQUID P.sum . P.map length $ -} lengths xs
        STRICT2(go)
        go []            _   = return ()
        go (PS p s l:ps) ptr = do
                -- LIQUID: could instead use  (also works)
                -- LIQUID {- invariant {v: [ByteString] | 0 <= (bLengths v)} -}
                let p'  = liquidAssert (lengths ps >= 0) p
                withForeignPtr p' $ \fp -> memcpy ptr (fp `plusPtr` s) (fromIntegral l)
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
               | otherwise = do let p' = liquid_thm_ptr_cmp p q     -- LIQUID
                                c <- peek p'
                                if f c then return True
                                       else go (p' `plusPtr` 1) q
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
               | otherwise  = do let p' = liquid_thm_ptr_cmp p q     -- LIQUID
                                 c <- peek p'
                                 if f c
                                    then go (p' `plusPtr` 1) q
                                    else return False
{-# INLINE all #-}

------------------------------------------------------------------------

-- | /O(n)/ 'maximum' returns the maximum value from a 'ByteString'
-- This function will fuse.
-- An exception will be thrown in the case of an empty ByteString.
{-@ maximum :: ByteStringNE -> Word8 @-}
maximum :: ByteString -> Word8
maximum xs@(PS x s l)
    | null xs   = errorEmptyList "maximum"
    | otherwise = inlinePerformIO $ withForeignPtr x $ \p ->
                      c_maximum (p `plusPtr` s) (fromIntegral l)
{-# INLINE maximum #-}

-- | /O(n)/ 'minimum' returns the minimum value from a 'ByteString'
-- This function will fuse.
-- An exception will be thrown in the case of an empty ByteString.
{-@ minimum :: ByteStringNE -> Word8 @-}
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

{-@ mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> b:ByteString -> (acc, ByteStringSZ b) @-}
mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
#if !defined(LOOPU_FUSION)
mapAccumL f z = unSP . loopUp (mapAccumEFL f) z
#else
mapAccumL f z = unSP . loopU (mapAccumEFL f) z
#endif
{-# INLINE mapAccumL #-}

-- | The 'mapAccumR' function behaves like a combination of 'map' and
-- 'foldr'; it applies a function to each element of a ByteString,
-- passing an accumulating parameter from right to left, and returning a
-- final value of this accumulator together with the new ByteString.

{-@ mapAccumR :: (acc -> Word8 -> (acc, Word8)) -> acc -> b:ByteString -> (acc, ByteStringSZ b) @-}
mapAccumR :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumR f z = unSP . loopDown (mapAccumEFL f) z
{-# INLINE mapAccumR #-}

-- | /O(n)/ map Word8 functions, provided with the index at each position
{-@ mapIndexed :: (Int -> Word8 -> Word8) -> ByteString -> ByteString @-}
mapIndexed :: (Int -> Word8 -> Word8) -> ByteString -> ByteString
mapIndexed f = loopArr . loopUp (mapIndexEFL f) 0
{-# INLINE mapIndexed #-}

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

{-@ scanl :: (Word8 -> Word8 -> Word8) -> Word8 -> b:ByteString
          -> {v:ByteString | (bLength v) = 1 + (bLength b)}
  @-}
scanl :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
#if !defined(LOOPU_FUSION)
scanl f z ps = loopArr . loopUp (scanEFL f) z $ (ps `snoc` 0)
#else
scanl f z ps = loopArr . loopU (scanEFL f) z $ (ps `snoc` 0)
#endif

    -- n.b. haskell's List scan returns a list one bigger than the
    -- input, so we need to snoc here to get some extra space, however,
    -- it breaks map/up fusion (i.e. scanl . map no longer fuses)
{-# INLINE scanl #-}

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
scanr f z ps = loopArr . loopDown (scanEFL (flip f)) z $ (0 `cons` ps) -- extra space
{-# INLINE scanr #-}

-- | 'scanr1' is a variant of 'scanr' that has no starting value argument.
scanr1 :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
scanr1 f ps
    | null ps   = empty
    | otherwise = scanr f (last ps) (init ps) -- todo, unsafe versions
{-# INLINE scanr1 #-}

-- ---------------------------------------------------------------------
-- LIQUID -- -- Unfolds and replicates
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ 'replicate' @n x@ is a ByteString of length @n@ with @x@
-- LIQUID -- -- the value of every element. The following holds:
-- LIQUID -- --
-- LIQUID -- -- > replicate w c = unfoldr w (\u -> Just (u,u)) c
-- LIQUID -- --
-- LIQUID -- -- This implemenation uses @memset(3)@
-- LIQUID -- replicate :: Int -> Word8 -> ByteString
-- LIQUID -- replicate w c
-- LIQUID --     | w <= 0    = empty
-- LIQUID --     | otherwise = unsafeCreate w $ \ptr ->
-- LIQUID --                       memset ptr c (fromIntegral w) >> return ()
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/, where /n/ is the length of the result.  The 'unfoldr' 
-- LIQUID -- -- function is analogous to the List \'unfoldr\'.  'unfoldr' builds a 
-- LIQUID -- -- ByteString from a seed value.  The function takes the element and 
-- LIQUID -- -- returns 'Nothing' if it is done producing the ByteString or returns 
-- LIQUID -- -- 'Just' @(a,b)@, in which case, @a@ is the next byte in the string, 
-- LIQUID -- -- and @b@ is the seed value for further production.
-- LIQUID -- --
-- LIQUID -- -- Examples:
-- LIQUID -- --
-- LIQUID -- -- >    unfoldr (\x -> if x <= 5 then Just (x, x + 1) else Nothing) 0
-- LIQUID -- -- > == pack [0, 1, 2, 3, 4, 5]
-- LIQUID -- --
-- LIQUID -- unfoldr :: (a -> Maybe (Word8, a)) -> a -> ByteString
-- LIQUID -- unfoldr f = concat . unfoldChunk 32 64
-- LIQUID --   where unfoldChunk n n' x =
-- LIQUID --           case unfoldrN n f x of
-- LIQUID --             (s, Nothing) -> s : []
-- LIQUID --             (s, Just x') -> s : unfoldChunk n' (n+n') x'
-- LIQUID -- {-# INLINE unfoldr #-}
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ Like 'unfoldr', 'unfoldrN' builds a ByteString from a seed
-- LIQUID -- -- value.  However, the length of the result is limited by the first
-- LIQUID -- -- argument to 'unfoldrN'.  This function is more efficient than 'unfoldr'
-- LIQUID -- -- when the maximum length of the result is known.
-- LIQUID -- --
-- LIQUID -- -- The following equation relates 'unfoldrN' and 'unfoldr':
-- LIQUID -- --
-- LIQUID -- -- > unfoldrN n f s == take n (unfoldr f s)
-- LIQUID -- --
-- LIQUID -- unfoldrN :: Int -> (a -> Maybe (Word8, a)) -> a -> (ByteString, Maybe a)
-- LIQUID -- unfoldrN i f x0
-- LIQUID --     | i < 0     = (empty, Just x0)
-- LIQUID --     | otherwise = unsafePerformIO $ createAndTrim' i $ \p -> go p x0 0
-- LIQUID --   where STRICT3(go)
-- LIQUID --         go p x n =
-- LIQUID --           case f x of
-- LIQUID --             Nothing      -> return (0, n, Nothing)
-- LIQUID --             Just (w,x')
-- LIQUID --              | n == i    -> return (0, n, Just x)
-- LIQUID --              | otherwise -> do poke p w
-- LIQUID --                                go (p `plusPtr` 1) x' (n+1)
-- LIQUID -- {-# INLINE unfoldrN #-}

-- ---------------------------------------------------------------------
-- Substrings

-- | /O(1)/ 'take' @n@, applied to a ByteString @xs@, returns the prefix
-- of @xs@ of length @n@, or @xs@ itself if @n > 'length' xs@.
{-@ take :: n:Nat
         -> b:ByteString
         -> {v:ByteString | (Min (bLength v) (bLength b) n)}
 @-}
take :: Int -> ByteString -> ByteString
take n ps@(PS x s l)
    | n <= 0    = empty
    | n >= l    = ps
    | otherwise = PS x s n
{-# INLINE take #-}

-- | /O(1)/ 'drop' @n xs@ returns the suffix of @xs@ after the first @n@
-- elements, or @[]@ if @n > 'length' xs@.
{-@ drop :: n:Nat
         -> b:ByteString
         -> {v:ByteString | ((bLength v) = (((bLength b) <= n)
                                         ? 0 : ((bLength b) - n)))}
  @-}
drop  :: Int -> ByteString -> ByteString
drop n ps@(PS x s l)
    | n <= 0    = ps
    | n >= l    = empty
    | otherwise = PS x (s+n) (l-n)
{-# INLINE drop #-}

-- | /O(1)/ 'splitAt' @n xs@ is equivalent to @('take' n xs, 'drop' n xs)@.
{-@ splitAt :: n:Nat
            -> b:ByteString
            -> ( {v:ByteString | (Min (bLength v) (bLength b) n)}
               , ByteString)<{\x y -> ((bLength y) = ((bLength b) - (bLength x)))}>
  @-}
splitAt :: Int -> ByteString -> (ByteString, ByteString)
splitAt n ps@(PS x s l)
    | n <= 0    = (empty, ps)
    | n >= l    = (ps, empty)
    | otherwise = (PS x s n, PS x (s+n) (l-n))
{-# INLINE splitAt #-}

-- LIQUID -- -- | 'takeWhile', applied to a predicate @p@ and a ByteString @xs@,
-- LIQUID -- -- returns the longest prefix (possibly empty) of @xs@ of elements that
-- LIQUID -- -- satisfy @p@.
-- LIQUID -- takeWhile :: (Word8 -> Bool) -> ByteString -> ByteString
-- LIQUID -- takeWhile f ps = unsafeTake (findIndexOrEnd (not . f) ps) ps
-- LIQUID -- {-# INLINE takeWhile #-}
-- LIQUID -- 
-- LIQUID -- -- | 'dropWhile' @p xs@ returns the suffix remaining after 'takeWhile' @p xs@.
-- LIQUID -- dropWhile :: (Word8 -> Bool) -> ByteString -> ByteString
-- LIQUID -- dropWhile f ps = unsafeDrop (findIndexOrEnd (not . f) ps) ps
-- LIQUID -- {-# INLINE dropWhile #-}
-- LIQUID -- 
-- LIQUID -- -- instead of findIndexOrEnd, we could use memchr here.
-- LIQUID -- 
-- LIQUID -- -- | 'break' @p@ is equivalent to @'span' ('not' . p)@.
-- LIQUID -- break :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
-- LIQUID -- break p ps = case findIndexOrEnd p ps of n -> (unsafeTake n ps, unsafeDrop n ps)
-- LIQUID -- #if __GLASGOW_HASKELL__ 
-- LIQUID -- {-# INLINE [1] break #-}
-- LIQUID -- 
-- LIQUID -- {-# RULES
-- LIQUID -- "FPS specialise break (x==)" forall x.
-- LIQUID --     break ((==) x) = breakByte x
-- LIQUID -- "FPS specialise break (==x)" forall x.
-- LIQUID --     break (==x) = breakByte x
-- LIQUID --   #-}
-- LIQUID -- #endif
-- LIQUID -- 
-- LIQUID -- -- | 'breakByte' breaks its ByteString argument at the first occurence
-- LIQUID -- -- of the specified byte. It is more efficient than 'break' as it is
-- LIQUID -- -- implemented with @memchr(3)@. I.e.
-- LIQUID -- -- 
-- LIQUID -- -- > break (=='c') "abcd" == breakByte 'c' "abcd"
-- LIQUID -- --
-- LIQUID -- breakByte :: Word8 -> ByteString -> (ByteString, ByteString)
-- LIQUID -- breakByte c p = case elemIndex c p of
-- LIQUID --     Nothing -> (p,empty)
-- LIQUID --     Just n  -> (unsafeTake n p, unsafeDrop n p)
-- LIQUID -- {-# INLINE breakByte #-}
-- LIQUID -- 
-- LIQUID -- -- | 'breakEnd' behaves like 'break' but from the end of the 'ByteString'
-- LIQUID -- -- 
-- LIQUID -- -- breakEnd p == spanEnd (not.p)
-- LIQUID -- breakEnd :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
-- LIQUID -- breakEnd  p ps = splitAt (findFromEndUntil p ps) ps
-- LIQUID -- 
-- LIQUID -- -- | 'span' @p xs@ breaks the ByteString into two segments. It is
-- LIQUID -- -- equivalent to @('takeWhile' p xs, 'dropWhile' p xs)@
-- LIQUID -- span :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
-- LIQUID -- span p ps = break (not . p) ps
-- LIQUID -- #if __GLASGOW_HASKELL__
-- LIQUID -- {-# INLINE [1] span #-}
-- LIQUID -- #endif
-- LIQUID -- 
-- LIQUID -- -- | 'spanByte' breaks its ByteString argument at the first
-- LIQUID -- -- occurence of a byte other than its argument. It is more efficient
-- LIQUID -- -- than 'span (==)'
-- LIQUID -- --
-- LIQUID -- -- > span  (=='c') "abcd" == spanByte 'c' "abcd"
-- LIQUID -- --
-- LIQUID -- spanByte :: Word8 -> ByteString -> (ByteString, ByteString)
-- LIQUID -- spanByte c ps@(PS x s l) = inlinePerformIO $ withForeignPtr x $ \p ->
-- LIQUID --     go (p `plusPtr` s) 0
-- LIQUID --   where
-- LIQUID --     STRICT2(go)
-- LIQUID --     go p i | i >= l    = return (ps, empty)
-- LIQUID --            | otherwise = do c' <- peekByteOff p i
-- LIQUID --                             if c /= c'
-- LIQUID --                                 then return (unsafeTake i ps, unsafeDrop i ps)
-- LIQUID --                                 else go p (i+1)
-- LIQUID -- {-# INLINE spanByte #-}
-- LIQUID -- 
-- LIQUID -- {-# RULES
-- LIQUID -- "FPS specialise span (x==)" forall x.
-- LIQUID --     span ((==) x) = spanByte x
-- LIQUID -- "FPS specialise span (==x)" forall x.
-- LIQUID --     span (==x) = spanByte x
-- LIQUID --   #-}
-- LIQUID -- 
-- LIQUID -- -- | 'spanEnd' behaves like 'span' but from the end of the 'ByteString'.
-- LIQUID -- -- We have
-- LIQUID -- --
-- LIQUID -- -- > spanEnd (not.isSpace) "x y z" == ("x y ","z")
-- LIQUID -- --
-- LIQUID -- -- and
-- LIQUID -- --
-- LIQUID -- -- > spanEnd (not . isSpace) ps
-- LIQUID -- -- >    == 
-- LIQUID -- -- > let (x,y) = span (not.isSpace) (reverse ps) in (reverse y, reverse x) 
-- LIQUID -- --
-- LIQUID -- spanEnd :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
-- LIQUID -- spanEnd  p ps = splitAt (findFromEndUntil (not.p) ps) ps
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ Splits a 'ByteString' into components delimited by
-- LIQUID -- -- separators, where the predicate returns True for a separator element.
-- LIQUID -- -- The resulting components do not contain the separators.  Two adjacent
-- LIQUID -- -- separators result in an empty component in the output.  eg.
-- LIQUID -- --
-- LIQUID -- -- > splitWith (=='a') "aabbaca" == ["","","bb","c",""]
-- LIQUID -- -- > splitWith (=='a') []        == []
-- LIQUID -- --
-- LIQUID -- splitWith :: (Word8 -> Bool) -> ByteString -> [ByteString]
-- LIQUID -- 
-- LIQUID -- #if defined(__GLASGOW_HASKELL__)
-- LIQUID -- splitWith _pred (PS _  _   0) = []
-- LIQUID -- splitWith pred_ (PS fp off len) = splitWith0 pred# off len fp
-- LIQUID --   where pred# c# = pred_ (W8# c#)
-- LIQUID -- 
-- LIQUID --         STRICT4(splitWith0)
-- LIQUID --         splitWith0 pred' off' len' fp' = withPtr fp $ \p ->
-- LIQUID --             splitLoop pred' p 0 off' len' fp'
-- LIQUID -- 
-- LIQUID --         splitLoop :: (Word# -> Bool)
-- LIQUID --                   -> Ptr Word8
-- LIQUID --                   -> Int -> Int -> Int
-- LIQUID --                   -> ForeignPtr Word8
-- LIQUID --                   -> IO [ByteString]
-- LIQUID -- 
-- LIQUID --         splitLoop pred' p idx' off' len' fp'
-- LIQUID --             | pred' `seq` p `seq` idx' `seq` off' `seq` len' `seq` fp' `seq` False = undefined
-- LIQUID --             | idx' >= len'  = return [PS fp' off' idx']
-- LIQUID --             | otherwise = do
-- LIQUID --                 w <- peekElemOff p (off'+idx')
-- LIQUID --                 if pred' (case w of W8# w# -> w#)
-- LIQUID --                    then return (PS fp' off' idx' :
-- LIQUID --                               splitWith0 pred' (off'+idx'+1) (len'-idx'-1) fp')
-- LIQUID --                    else splitLoop pred' p (idx'+1) off' len' fp'
-- LIQUID -- {-# INLINE splitWith #-}
-- LIQUID -- 
-- LIQUID -- #else
-- LIQUID -- splitWith _ (PS _ _ 0) = []
-- LIQUID -- splitWith p ps = loop p ps
-- LIQUID --     where
-- LIQUID --         STRICT2(loop)
-- LIQUID --         loop q qs = if null rest then [chunk]
-- LIQUID --                                  else chunk : loop q (unsafeTail rest)
-- LIQUID --             where (chunk,rest) = break q qs
-- LIQUID -- #endif
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ Break a 'ByteString' into pieces separated by the byte
-- LIQUID -- -- argument, consuming the delimiter. I.e.
-- LIQUID -- --
-- LIQUID -- -- > split '\n' "a\nb\nd\ne" == ["a","b","d","e"]
-- LIQUID -- -- > split 'a'  "aXaXaXa"    == ["","X","X","X",""]
-- LIQUID -- -- > split 'x'  "x"          == ["",""]
-- LIQUID -- -- 
-- LIQUID -- -- and
-- LIQUID -- --
-- LIQUID -- -- > intercalate [c] . split c == id
-- LIQUID -- -- > split == splitWith . (==)
-- LIQUID -- -- 
-- LIQUID -- -- As for all splitting functions in this library, this function does
-- LIQUID -- -- not copy the substrings, it just constructs new 'ByteStrings' that
-- LIQUID -- -- are slices of the original.
-- LIQUID -- --
-- LIQUID -- split :: Word8 -> ByteString -> [ByteString]
-- LIQUID -- split _ (PS _ _ 0) = []
-- LIQUID -- split w (PS x s l) = inlinePerformIO $ withForeignPtr x $ \p -> do
-- LIQUID --     let ptr = p `plusPtr` s
-- LIQUID -- 
-- LIQUID --         STRICT1(loop)
-- LIQUID --         loop n =
-- LIQUID --             let q = inlinePerformIO $ memchr (ptr `plusPtr` n)
-- LIQUID --                                            w (fromIntegral (l-n))
-- LIQUID --             in if q == nullPtr
-- LIQUID --                 then [PS x (s+n) (l-n)]
-- LIQUID --                 else let i = q `minusPtr` ptr in PS x (s+n) (i-n) : loop (i+1)
-- LIQUID -- 
-- LIQUID --     return (loop 0)
-- LIQUID -- {-# INLINE split #-}
-- LIQUID -- 
-- LIQUID -- {-
-- LIQUID -- -- slower. but stays inside Haskell.
-- LIQUID -- split _ (PS _  _   0) = []
-- LIQUID -- split (W8# w#) (PS fp off len) = splitWith' off len fp
-- LIQUID --     where
-- LIQUID --         splitWith' off' len' fp' = withPtr fp $ \p ->
-- LIQUID --             splitLoop p 0 off' len' fp'
-- LIQUID -- 
-- LIQUID --         splitLoop :: Ptr Word8
-- LIQUID --                   -> Int -> Int -> Int
-- LIQUID --                   -> ForeignPtr Word8
-- LIQUID --                   -> IO [ByteString]
-- LIQUID -- 
-- LIQUID --         STRICT5(splitLoop)
-- LIQUID --         splitLoop p idx' off' len' fp'
-- LIQUID --             | p `seq` idx' `seq` off' `seq` len' `seq` fp' `seq` False = undefined
-- LIQUID --             | idx' >= len'  = return [PS fp' off' idx']
-- LIQUID --             | otherwise = do
-- LIQUID --                 (W8# x#) <- peekElemOff p (off'+idx')
-- LIQUID --                 if word2Int# w# ==# word2Int# x#
-- LIQUID --                    then return (PS fp' off' idx' :
-- LIQUID --                               splitWith' (off'+idx'+1) (len'-idx'-1) fp')
-- LIQUID --                    else splitLoop p (idx'+1) off' len' fp'
-- LIQUID -- -}
-- LIQUID -- 
-- LIQUID -- {-
-- LIQUID -- -- | Like 'splitWith', except that sequences of adjacent separators are
-- LIQUID -- -- treated as a single separator. eg.
-- LIQUID -- -- 
-- LIQUID -- -- > tokens (=='a') "aabbaca" == ["bb","c"]
-- LIQUID -- --
-- LIQUID -- tokens :: (Word8 -> Bool) -> ByteString -> [ByteString]
-- LIQUID -- tokens f = P.filter (not.null) . splitWith f
-- LIQUID -- {-# INLINE tokens #-}
-- LIQUID -- -}
-- LIQUID -- 
-- LIQUID -- -- | The 'group' function takes a ByteString and returns a list of
-- LIQUID -- -- ByteStrings such that the concatenation of the result is equal to the
-- LIQUID -- -- argument.  Moreover, each sublist in the result contains only equal
-- LIQUID -- -- elements.  For example,
-- LIQUID -- --
-- LIQUID -- -- > group "Mississippi" = ["M","i","ss","i","ss","i","pp","i"]
-- LIQUID -- --
-- LIQUID -- -- It is a special case of 'groupBy', which allows the programmer to
-- LIQUID -- -- supply their own equality test. It is about 40% faster than 
-- LIQUID -- -- /groupBy (==)/
-- LIQUID -- group :: ByteString -> [ByteString]
-- LIQUID -- group xs
-- LIQUID --     | null xs   = []
-- LIQUID --     | otherwise = ys : group zs
-- LIQUID --     where
-- LIQUID --         (ys, zs) = spanByte (unsafeHead xs) xs
-- LIQUID -- 
-- LIQUID -- -- | The 'groupBy' function is the non-overloaded version of 'group'.
-- LIQUID -- groupBy :: (Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]
-- LIQUID -- groupBy k xs
-- LIQUID --     | null xs   = []
-- LIQUID --     | otherwise = unsafeTake n xs : groupBy k (unsafeDrop n xs)
-- LIQUID --     where
-- LIQUID --         n = 1 + findIndexOrEnd (not . k (unsafeHead xs)) (unsafeTail xs)
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ The 'intercalate' function takes a 'ByteString' and a list of
-- LIQUID -- -- 'ByteString's and concatenates the list after interspersing the first
-- LIQUID -- -- argument between each element of the list.
-- LIQUID -- intercalate :: ByteString -> [ByteString] -> ByteString
-- LIQUID -- intercalate s = concat . (List.intersperse s)
-- LIQUID -- {-# INLINE [1] intercalate #-}
-- LIQUID -- 
-- LIQUID -- join :: ByteString -> [ByteString] -> ByteString
-- LIQUID -- join = intercalate
-- LIQUID -- {-# DEPRECATED join "use intercalate" #-}
-- LIQUID -- 
-- LIQUID -- {-# RULES
-- LIQUID -- "FPS specialise intercalate c -> intercalateByte" forall c s1 s2 .
-- LIQUID --     intercalate (singleton c) (s1 : s2 : []) = intercalateWithByte c s1 s2
-- LIQUID --   #-}
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ intercalateWithByte. An efficient way to join to two ByteStrings
-- LIQUID -- -- with a char. Around 4 times faster than the generalised join.
-- LIQUID -- --
-- LIQUID -- intercalateWithByte :: Word8 -> ByteString -> ByteString -> ByteString
-- LIQUID -- intercalateWithByte c f@(PS ffp s l) g@(PS fgp t m) = unsafeCreate len $ \ptr ->
-- LIQUID --     withForeignPtr ffp $ \fp ->
-- LIQUID --     withForeignPtr fgp $ \gp -> do
-- LIQUID --         memcpy ptr (fp `plusPtr` s) (fromIntegral l)
-- LIQUID --         poke (ptr `plusPtr` l) c
-- LIQUID --         memcpy (ptr `plusPtr` (l + 1)) (gp `plusPtr` t) (fromIntegral m)
-- LIQUID --     where
-- LIQUID --       len = length f + length g + 1
-- LIQUID -- {-# INLINE intercalateWithByte #-}
-- LIQUID -- 
-- LIQUID -- -- ---------------------------------------------------------------------
-- LIQUID -- -- Indexing ByteStrings
-- LIQUID -- 
-- LIQUID -- -- | /O(1)/ 'ByteString' index (subscript) operator, starting from 0.
-- LIQUID -- index :: ByteString -> Int -> Word8
-- LIQUID -- index ps n
-- LIQUID --     | n < 0          = moduleError "index" ("negative index: " ++ show n)
-- LIQUID --     | n >= length ps = moduleError "index" ("index too large: " ++ show n
-- LIQUID --                                          ++ ", length = " ++ show (length ps))
-- LIQUID --     | otherwise      = ps `unsafeIndex` n
-- LIQUID -- {-# INLINE index #-}
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ The 'elemIndex' function returns the index of the first
-- LIQUID -- -- element in the given 'ByteString' which is equal to the query
-- LIQUID -- -- element, or 'Nothing' if there is no such element. 
-- LIQUID -- -- This implementation uses memchr(3).
-- LIQUID -- elemIndex :: Word8 -> ByteString -> Maybe Int
-- LIQUID -- elemIndex c (PS x s l) = inlinePerformIO $ withForeignPtr x $ \p -> do
-- LIQUID --     let p' = p `plusPtr` s
-- LIQUID --     q <- memchr p' c (fromIntegral l)
-- LIQUID --     return $! if q == nullPtr then Nothing else Just $! q `minusPtr` p'
-- LIQUID -- {-# INLINE elemIndex #-}
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ The 'elemIndexEnd' function returns the last index of the
-- LIQUID -- -- element in the given 'ByteString' which is equal to the query
-- LIQUID -- -- element, or 'Nothing' if there is no such element. The following
-- LIQUID -- -- holds:
-- LIQUID -- --
-- LIQUID -- -- > elemIndexEnd c xs == 
-- LIQUID -- -- > (-) (length xs - 1) `fmap` elemIndex c (reverse xs)
-- LIQUID -- --
-- LIQUID -- elemIndexEnd :: Word8 -> ByteString -> Maybe Int
-- LIQUID -- elemIndexEnd ch (PS x s l) = inlinePerformIO $ withForeignPtr x $ \p ->
-- LIQUID --     go (p `plusPtr` s) (l-1)
-- LIQUID --   where
-- LIQUID --     STRICT2(go)
-- LIQUID --     go p i | i < 0     = return Nothing
-- LIQUID --            | otherwise = do ch' <- peekByteOff p i
-- LIQUID --                             if ch == ch'
-- LIQUID --                                 then return $ Just i
-- LIQUID --                                 else go p (i-1)
-- LIQUID -- {-# INLINE elemIndexEnd #-}
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ The 'elemIndices' function extends 'elemIndex', by returning
-- LIQUID -- -- the indices of all elements equal to the query element, in ascending order.
-- LIQUID -- -- This implementation uses memchr(3).
-- LIQUID -- elemIndices :: Word8 -> ByteString -> [Int]
-- LIQUID -- elemIndices w (PS x s l) = inlinePerformIO $ withForeignPtr x $ \p -> do
-- LIQUID --     let ptr = p `plusPtr` s
-- LIQUID -- 
-- LIQUID --         STRICT1(loop)
-- LIQUID --         loop n = let q = inlinePerformIO $ memchr (ptr `plusPtr` n)
-- LIQUID --                                                 w (fromIntegral (l - n))
-- LIQUID --                  in if q == nullPtr
-- LIQUID --                         then []
-- LIQUID --                         else let i = q `minusPtr` ptr
-- LIQUID --                              in i : loop (i+1)
-- LIQUID --     return $! loop 0
-- LIQUID -- {-# INLINE elemIndices #-}
-- LIQUID -- 
-- LIQUID -- {-
-- LIQUID -- -- much slower
-- LIQUID -- elemIndices :: Word8 -> ByteString -> [Int]
-- LIQUID -- elemIndices c ps = loop 0 ps
-- LIQUID --    where STRICT2(loop)
-- LIQUID --          loop _ ps' | null ps'            = []
-- LIQUID --          loop n ps' | c == unsafeHead ps' = n : loop (n+1) (unsafeTail ps')
-- LIQUID --                     | otherwise           = loop (n+1) (unsafeTail ps')
-- LIQUID -- -}
-- LIQUID -- 
-- LIQUID -- -- | count returns the number of times its argument appears in the ByteString
-- LIQUID -- --
-- LIQUID -- -- > count = length . elemIndices
-- LIQUID -- --
-- LIQUID -- -- But more efficiently than using length on the intermediate list.
-- LIQUID -- count :: Word8 -> ByteString -> Int
-- LIQUID -- count w (PS x s m) = inlinePerformIO $ withForeignPtr x $ \p ->
-- LIQUID --     fmap fromIntegral $ c_count (p `plusPtr` s) (fromIntegral m) w
-- LIQUID -- {-# INLINE count #-}
-- LIQUID -- 
-- LIQUID -- {-
-- LIQUID -- --
-- LIQUID -- -- around 30% slower
-- LIQUID -- --
-- LIQUID -- count w (PS x s m) = inlinePerformIO $ withForeignPtr x $ \p ->
-- LIQUID --      go (p `plusPtr` s) (fromIntegral m) 0
-- LIQUID --     where
-- LIQUID --         go :: Ptr Word8 -> CSize -> Int -> IO Int
-- LIQUID --         STRICT3(go)
-- LIQUID --         go p l i = do
-- LIQUID --             q <- memchr p w l
-- LIQUID --             if q == nullPtr
-- LIQUID --                 then return i
-- LIQUID --                 else do let k = fromIntegral $ q `minusPtr` p
-- LIQUID --                         go (q `plusPtr` 1) (l-k-1) (i+1)
-- LIQUID -- -}
-- LIQUID -- 
-- LIQUID -- -- | The 'findIndex' function takes a predicate and a 'ByteString' and
-- LIQUID -- -- returns the index of the first element in the ByteString
-- LIQUID -- -- satisfying the predicate.
-- LIQUID -- findIndex :: (Word8 -> Bool) -> ByteString -> Maybe Int
-- LIQUID -- findIndex k (PS x s l) = inlinePerformIO $ withForeignPtr x $ \f -> go (f `plusPtr` s) 0
-- LIQUID --   where
-- LIQUID --     STRICT2(go)
-- LIQUID --     go ptr n | n >= l    = return Nothing
-- LIQUID --              | otherwise = do w <- peek ptr
-- LIQUID --                               if k w
-- LIQUID --                                 then return (Just n)
-- LIQUID --                                 else go (ptr `plusPtr` 1) (n+1)
-- LIQUID -- {-# INLINE findIndex #-}
-- LIQUID -- 
-- LIQUID -- -- | The 'findIndices' function extends 'findIndex', by returning the
-- LIQUID -- -- indices of all elements satisfying the predicate, in ascending order.
-- LIQUID -- findIndices :: (Word8 -> Bool) -> ByteString -> [Int]
-- LIQUID -- findIndices p ps = loop 0 ps
-- LIQUID --    where
-- LIQUID --      STRICT2(loop)
-- LIQUID --      loop n qs | null qs           = []
-- LIQUID --                | p (unsafeHead qs) = n : loop (n+1) (unsafeTail qs)
-- LIQUID --                | otherwise         =     loop (n+1) (unsafeTail qs)
-- LIQUID -- 
-- LIQUID -- -- ---------------------------------------------------------------------
-- LIQUID -- -- Searching ByteStrings
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ 'elem' is the 'ByteString' membership predicate.
-- LIQUID -- elem :: Word8 -> ByteString -> Bool
-- LIQUID -- elem c ps = case elemIndex c ps of Nothing -> False ; _ -> True
-- LIQUID -- {-# INLINE elem #-}
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ 'notElem' is the inverse of 'elem'
-- LIQUID -- notElem :: Word8 -> ByteString -> Bool
-- LIQUID -- notElem c ps = not (elem c ps)
-- LIQUID -- {-# INLINE notElem #-}
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ 'filter', applied to a predicate and a ByteString,
-- LIQUID -- -- returns a ByteString containing those characters that satisfy the
-- LIQUID -- -- predicate. This function is subject to array fusion.
-- LIQUID -- filter :: (Word8 -> Bool) -> ByteString -> ByteString
-- LIQUID -- filter k ps@(PS x s l)
-- LIQUID --     | null ps   = ps
-- LIQUID --     | otherwise = unsafePerformIO $ createAndTrim l $ \p -> withForeignPtr x $ \f -> do
-- LIQUID --         t <- go (f `plusPtr` s) p (f `plusPtr` (s + l))
-- LIQUID --         return $! t `minusPtr` p -- actual length
-- LIQUID --     where
-- LIQUID --         STRICT3(go)
-- LIQUID --         go f t end | f == end  = return t
-- LIQUID --                    | otherwise = do
-- LIQUID --                         w <- peek f
-- LIQUID --                         if k w
-- LIQUID --                             then poke t w >> go (f `plusPtr` 1) (t `plusPtr` 1) end
-- LIQUID --                             else             go (f `plusPtr` 1) t               end
-- LIQUID -- #if __GLASGOW_HASKELL__
-- LIQUID -- {-# INLINE [1] filter #-}
-- LIQUID -- #endif
-- LIQUID -- 
-- LIQUID -- --
-- LIQUID -- -- | /O(n)/ A first order equivalent of /filter . (==)/, for the common
-- LIQUID -- -- case of filtering a single byte. It is more efficient to use
-- LIQUID -- -- /filterByte/ in this case.
-- LIQUID -- --
-- LIQUID -- -- > filterByte == filter . (==)
-- LIQUID -- --
-- LIQUID -- -- filterByte is around 10x faster, and uses much less space, than its
-- LIQUID -- -- filter equivalent
-- LIQUID -- --
-- LIQUID -- filterByte :: Word8 -> ByteString -> ByteString
-- LIQUID -- filterByte w ps = replicate (count w ps) w
-- LIQUID -- {-# INLINE filterByte #-}
-- LIQUID -- 
-- LIQUID -- {-# RULES
-- LIQUID --   "FPS specialise filter (== x)" forall x.
-- LIQUID --       filter ((==) x) = filterByte x
-- LIQUID --   #-}
-- LIQUID -- 
-- LIQUID -- {-# RULES
-- LIQUID --   "FPS specialise filter (== x)" forall x.
-- LIQUID --      filter (== x) = filterByte x
-- LIQUID --   #-}
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ The 'find' function takes a predicate and a ByteString,
-- LIQUID -- -- and returns the first element in matching the predicate, or 'Nothing'
-- LIQUID -- -- if there is no such element.
-- LIQUID -- --
-- LIQUID -- -- > find f p = case findIndex f p of Just n -> Just (p ! n) ; _ -> Nothing
-- LIQUID -- --
-- LIQUID -- find :: (Word8 -> Bool) -> ByteString -> Maybe Word8
-- LIQUID -- find f p = case findIndex f p of
-- LIQUID --                     Just n -> Just (p `unsafeIndex` n)
-- LIQUID --                     _      -> Nothing
-- LIQUID -- {-# INLINE find #-}
-- LIQUID -- 
-- LIQUID -- {-
-- LIQUID -- --
-- LIQUID -- -- fuseable, but we don't want to walk the whole array.
-- LIQUID -- -- 
-- LIQUID -- find k = foldl findEFL Nothing
-- LIQUID --     where findEFL a@(Just _) _ = a
-- LIQUID --           findEFL _          c | k c       = Just c
-- LIQUID --                                | otherwise = Nothing
-- LIQUID -- -}
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ The 'partition' function takes a predicate a ByteString and returns
-- LIQUID -- -- the pair of ByteStrings with elements which do and do not satisfy the
-- LIQUID -- -- predicate, respectively; i.e.,
-- LIQUID -- --
-- LIQUID -- -- > partition p bs == (filter p xs, filter (not . p) xs)
-- LIQUID -- --
-- LIQUID -- partition :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
-- LIQUID -- partition p bs = (filter p bs, filter (not . p) bs)
-- LIQUID -- --TODO: use a better implementation
-- LIQUID -- 
-- LIQUID -- -- ---------------------------------------------------------------------
-- LIQUID -- -- Searching for substrings
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ The 'isPrefixOf' function takes two ByteStrings and returns 'True'
-- LIQUID -- -- iff the first is a prefix of the second.
-- LIQUID -- isPrefixOf :: ByteString -> ByteString -> Bool
-- LIQUID -- isPrefixOf (PS x1 s1 l1) (PS x2 s2 l2)
-- LIQUID --     | l1 == 0   = True
-- LIQUID --     | l2 < l1   = False
-- LIQUID --     | otherwise = inlinePerformIO $ withForeignPtr x1 $ \p1 ->
-- LIQUID --         withForeignPtr x2 $ \p2 -> do
-- LIQUID --             i <- memcmp (p1 `plusPtr` s1) (p2 `plusPtr` s2) (fromIntegral l1)
-- LIQUID --             return $! i == 0
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ The 'isSuffixOf' function takes two ByteStrings and returns 'True'
-- LIQUID -- -- iff the first is a suffix of the second.
-- LIQUID -- -- 
-- LIQUID -- -- The following holds:
-- LIQUID -- --
-- LIQUID -- -- > isSuffixOf x y == reverse x `isPrefixOf` reverse y
-- LIQUID -- --
-- LIQUID -- -- However, the real implemenation uses memcmp to compare the end of the
-- LIQUID -- -- string only, with no reverse required..
-- LIQUID -- isSuffixOf :: ByteString -> ByteString -> Bool
-- LIQUID -- isSuffixOf (PS x1 s1 l1) (PS x2 s2 l2)
-- LIQUID --     | l1 == 0   = True
-- LIQUID --     | l2 < l1   = False
-- LIQUID --     | otherwise = inlinePerformIO $ withForeignPtr x1 $ \p1 ->
-- LIQUID --         withForeignPtr x2 $ \p2 -> do
-- LIQUID --             i <- memcmp (p1 `plusPtr` s1) (p2 `plusPtr` s2 `plusPtr` (l2 - l1)) (fromIntegral l1)
-- LIQUID --             return $! i == 0
-- LIQUID -- 
-- LIQUID -- -- | Alias of 'isSubstringOf'
-- LIQUID -- isInfixOf :: ByteString -> ByteString -> Bool
-- LIQUID -- isInfixOf = isSubstringOf
-- LIQUID -- 
-- LIQUID -- -- | Check whether one string is a substring of another. @isSubstringOf
-- LIQUID -- -- p s@ is equivalent to @not (null (findSubstrings p s))@.
-- LIQUID -- isSubstringOf :: ByteString -- ^ String to search for.
-- LIQUID --               -> ByteString -- ^ String to search in.
-- LIQUID --               -> Bool
-- LIQUID -- isSubstringOf p s = not $ P.null $ findSubstrings p s
-- LIQUID -- 
-- LIQUID -- {-# DEPRECATED findSubstring "Do not use. The ByteString searching api is about to be replaced." #-}
-- LIQUID -- -- | Get the first index of a substring in another string,
-- LIQUID -- --   or 'Nothing' if the string is not found.
-- LIQUID -- --   @findSubstring p s@ is equivalent to @listToMaybe (findSubstrings p s)@.
-- LIQUID -- findSubstring :: ByteString -- ^ String to search for.
-- LIQUID --               -> ByteString -- ^ String to seach in.
-- LIQUID --               -> Maybe Int
-- LIQUID -- findSubstring = (listToMaybe .) . findSubstrings
-- LIQUID -- 
-- LIQUID -- {-# DEPRECATED findSubstrings "Do not use. The ByteString searching api is about to be replaced." #-}
-- LIQUID -- -- | Find the indexes of all (possibly overlapping) occurances of a
-- LIQUID -- -- substring in a string.  This function uses the Knuth-Morris-Pratt
-- LIQUID -- -- string matching algorithm.
-- LIQUID -- findSubstrings :: ByteString -- ^ String to search for.
-- LIQUID --                -> ByteString -- ^ String to seach in.
-- LIQUID --                -> [Int]
-- LIQUID -- 
-- LIQUID -- findSubstrings pat@(PS _ _ m) str@(PS _ _ n) = search 0 0
-- LIQUID --   where
-- LIQUID --       patc x = pat `unsafeIndex` x
-- LIQUID --       strc x = str `unsafeIndex` x
-- LIQUID -- 
-- LIQUID --       -- maybe we should make kmpNext a UArray before using it in search?
-- LIQUID --       kmpNext = listArray (0,m) (-1:kmpNextL pat (-1))
-- LIQUID --       kmpNextL p _ | null p = []
-- LIQUID --       kmpNextL p j = let j' = next (unsafeHead p) j + 1
-- LIQUID --                          ps = unsafeTail p
-- LIQUID --                          x = if not (null ps) && unsafeHead ps == patc j'
-- LIQUID --                                 then kmpNext Array.! j' else j'
-- LIQUID --                         in x:kmpNextL ps j'
-- LIQUID --       search i j = match ++ rest -- i: position in string, j: position in pattern
-- LIQUID --         where match = if j == m then [(i - j)] else []
-- LIQUID --               rest = if i == n then [] else search (i+1) (next (strc i) j + 1)
-- LIQUID --       next c j | j >= 0 && (j == m || c /= patc j) = next c (kmpNext Array.! j)
-- LIQUID --                | otherwise = j
-- LIQUID -- 
-- LIQUID -- -- ---------------------------------------------------------------------
-- LIQUID -- -- Zipping
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ 'zip' takes two ByteStrings and returns a list of
-- LIQUID -- -- corresponding pairs of bytes. If one input ByteString is short,
-- LIQUID -- -- excess elements of the longer ByteString are discarded. This is
-- LIQUID -- -- equivalent to a pair of 'unpack' operations.
-- LIQUID -- zip :: ByteString -> ByteString -> [(Word8,Word8)]
-- LIQUID -- zip ps qs
-- LIQUID --     | null ps || null qs = []
-- LIQUID --     | otherwise = (unsafeHead ps, unsafeHead qs) : zip (unsafeTail ps) (unsafeTail qs)
-- LIQUID -- 
-- LIQUID -- -- | 'zipWith' generalises 'zip' by zipping with the function given as
-- LIQUID -- -- the first argument, instead of a tupling function.  For example,
-- LIQUID -- -- @'zipWith' (+)@ is applied to two ByteStrings to produce the list of
-- LIQUID -- -- corresponding sums. 
-- LIQUID -- zipWith :: (Word8 -> Word8 -> a) -> ByteString -> ByteString -> [a]
-- LIQUID -- zipWith f ps qs
-- LIQUID --     | null ps || null qs = []
-- LIQUID --     | otherwise = f (unsafeHead ps) (unsafeHead qs) : zipWith f (unsafeTail ps) (unsafeTail qs)
-- LIQUID -- #if defined(__GLASGOW_HASKELL__)
-- LIQUID -- {-# INLINE [1] zipWith #-}
-- LIQUID -- #endif
-- LIQUID -- 
-- LIQUID -- --
-- LIQUID -- -- | A specialised version of zipWith for the common case of a
-- LIQUID -- -- simultaneous map over two bytestrings, to build a 3rd. Rewrite rules
-- LIQUID -- -- are used to automatically covert zipWith into zipWith' when a pack is
-- LIQUID -- -- performed on the result of zipWith, but we also export it for
-- LIQUID -- -- convenience.
-- LIQUID -- --
-- LIQUID -- zipWith' :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString -> ByteString
-- LIQUID -- zipWith' f (PS fp s l) (PS fq t m) = inlinePerformIO $
-- LIQUID --     withForeignPtr fp $ \a ->
-- LIQUID --     withForeignPtr fq $ \b ->
-- LIQUID --     create len $ zipWith_ 0 (a `plusPtr` s) (b `plusPtr` t)
-- LIQUID --   where
-- LIQUID --     zipWith_ :: Int -> Ptr Word8 -> Ptr Word8 -> Ptr Word8 -> IO ()
-- LIQUID --     STRICT4(zipWith_)
-- LIQUID --     zipWith_ n p1 p2 r
-- LIQUID --        | n >= len = return ()
-- LIQUID --        | otherwise = do
-- LIQUID --             x <- peekByteOff p1 n
-- LIQUID --             y <- peekByteOff p2 n
-- LIQUID --             pokeByteOff r n (f x y)
-- LIQUID --             zipWith_ (n+1) p1 p2 r
-- LIQUID -- 
-- LIQUID --     len = min l m
-- LIQUID -- {-# INLINE zipWith' #-}
-- LIQUID -- 
-- LIQUID -- {-# RULES
-- LIQUID -- 
-- LIQUID -- "FPS specialise zipWith" forall (f :: Word8 -> Word8 -> Word8) p q .
-- LIQUID --     zipWith f p q = unpack (zipWith' f p q)
-- LIQUID -- 
-- LIQUID --   #-}
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ 'unzip' transforms a list of pairs of bytes into a pair of
-- LIQUID -- -- ByteStrings. Note that this performs two 'pack' operations.
-- LIQUID -- unzip :: [(Word8,Word8)] -> (ByteString,ByteString)
-- LIQUID -- unzip ls = (pack (P.map fst ls), pack (P.map snd ls))
-- LIQUID -- {-# INLINE unzip #-}
-- LIQUID -- 
-- LIQUID -- -- ---------------------------------------------------------------------
-- LIQUID -- -- Special lists
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ Return all initial segments of the given 'ByteString', shortest first.
-- LIQUID -- inits :: ByteString -> [ByteString]
-- LIQUID -- inits (PS x s l) = [PS x s n | n <- [0..l]]
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ Return all final segments of the given 'ByteString', longest first.
-- LIQUID -- tails :: ByteString -> [ByteString]
-- LIQUID -- tails p | null p    = [empty]
-- LIQUID --         | otherwise = p : tails (unsafeTail p)
-- LIQUID -- 
-- LIQUID -- -- less efficent spacewise: tails (PS x s l) = [PS x (s+n) (l-n) | n <- [0..l]]
-- LIQUID -- 
-- LIQUID -- -- ---------------------------------------------------------------------
-- LIQUID -- -- ** Ordered 'ByteString's
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ Sort a ByteString efficiently, using counting sort.
-- LIQUID -- sort :: ByteString -> ByteString
-- LIQUID -- sort (PS input s l) = unsafeCreate l $ \p -> allocaArray 256 $ \arr -> do
-- LIQUID -- 
-- LIQUID --     memset (castPtr arr) 0 (256 * fromIntegral (sizeOf (undefined :: CSize)))
-- LIQUID --     withForeignPtr input (\x -> countOccurrences arr (x `plusPtr` s) l)
-- LIQUID -- 
-- LIQUID --     let STRICT2(go)
-- LIQUID --         go 256 _   = return ()
-- LIQUID --         go i   ptr = do n <- peekElemOff arr i
-- LIQUID --                         when (n /= 0) $ memset ptr (fromIntegral i) n >> return ()
-- LIQUID --                         go (i + 1) (ptr `plusPtr` (fromIntegral n))
-- LIQUID --     go 0 p
-- LIQUID --   where
-- LIQUID --     -- | Count the number of occurrences of each byte.
-- LIQUID --     -- Used by 'sort'
-- LIQUID --     --
-- LIQUID --     countOccurrences :: Ptr CSize -> Ptr Word8 -> Int -> IO ()
-- LIQUID --     STRICT3(countOccurrences)
-- LIQUID --     countOccurrences counts str len = go 0
-- LIQUID --      where
-- LIQUID --         STRICT1(go)
-- LIQUID --         go i | i == len    = return ()
-- LIQUID --              | otherwise = do k <- fromIntegral `fmap` peekElemOff str i
-- LIQUID --                               x <- peekElemOff counts k
-- LIQUID --                               pokeElemOff counts k (x + 1)
-- LIQUID --                               go (i + 1)
-- LIQUID -- 
-- LIQUID -- {-
-- LIQUID -- sort :: ByteString -> ByteString
-- LIQUID -- sort (PS x s l) = unsafeCreate l $ \p -> withForeignPtr x $ \f -> do
-- LIQUID --         memcpy p (f `plusPtr` s) l
-- LIQUID --         c_qsort p l -- inplace
-- LIQUID -- -}
-- LIQUID -- 
-- LIQUID -- -- The 'sortBy' function is the non-overloaded version of 'sort'.
-- LIQUID -- --
-- LIQUID -- -- Try some linear sorts: radix, counting
-- LIQUID -- -- Or mergesort.
-- LIQUID -- --
-- LIQUID -- -- sortBy :: (Word8 -> Word8 -> Ordering) -> ByteString -> ByteString
-- LIQUID -- -- sortBy f ps = undefined
-- LIQUID -- 
-- LIQUID -- -- ---------------------------------------------------------------------
-- LIQUID -- -- Low level constructors
-- LIQUID -- 
-- LIQUID -- -- | /O(n) construction/ Use a @ByteString@ with a function requiring a
-- LIQUID -- -- null-terminated @CString@.  The @CString@ will be freed
-- LIQUID -- -- automatically. This is a memcpy(3).
-- LIQUID -- useAsCString :: ByteString -> (CString -> IO a) -> IO a
-- LIQUID -- useAsCString (PS fp o l) action = do
-- LIQUID --  allocaBytes (l+1) $ \buf ->
-- LIQUID --    withForeignPtr fp $ \p -> do
-- LIQUID --      memcpy buf (p `plusPtr` o) (fromIntegral l)
-- LIQUID --      pokeByteOff buf l (0::Word8)
-- LIQUID --      action (castPtr buf)
-- LIQUID -- 
-- LIQUID -- -- | /O(n) construction/ Use a @ByteString@ with a function requiring a @CStringLen@.
-- LIQUID -- -- As for @useAsCString@ this function makes a copy of the original @ByteString@.
-- LIQUID -- useAsCStringLen :: ByteString -> (CStringLen -> IO a) -> IO a
-- LIQUID -- useAsCStringLen p@(PS _ _ l) f = useAsCString p $ \cstr -> f (cstr,l)
-- LIQUID -- 
-- LIQUID -- ------------------------------------------------------------------------
-- LIQUID -- 
-- LIQUID -- -- | /O(n)./ Construct a new @ByteString@ from a @CString@. The
-- LIQUID -- -- resulting @ByteString@ is an immutable copy of the original
-- LIQUID -- -- @CString@, and is managed on the Haskell heap. The original
-- LIQUID -- -- @CString@ must be null terminated.
-- LIQUID -- packCString :: CString -> IO ByteString
-- LIQUID -- packCString cstr = do
-- LIQUID --     len <- c_strlen cstr
-- LIQUID --     packCStringLen (cstr, fromIntegral len)
-- LIQUID -- 
-- LIQUID -- -- | /O(n)./ Construct a new @ByteString@ from a @CStringLen@. The
-- LIQUID -- -- resulting @ByteString@ is an immutable copy of the original @CStringLen@.
-- LIQUID -- -- The @ByteString@ is a normal Haskell value and will be managed on the
-- LIQUID -- -- Haskell heap.
-- LIQUID -- packCStringLen :: CStringLen -> IO ByteString
-- LIQUID -- packCStringLen (cstr, len) = create len $ \p ->
-- LIQUID --     memcpy p (castPtr cstr) (fromIntegral len)
-- LIQUID -- 
-- LIQUID -- ------------------------------------------------------------------------
-- LIQUID -- 
-- LIQUID -- -- | /O(n)/ Make a copy of the 'ByteString' with its own storage. 
-- LIQUID -- -- This is mainly useful to allow the rest of the data pointed
-- LIQUID -- -- to by the 'ByteString' to be garbage collected, for example
-- LIQUID -- -- if a large string has been read in, and only a small part of it 
-- LIQUID -- -- is needed in the rest of the program.
-- LIQUID -- -- 
-- LIQUID -- copy :: ByteString -> ByteString
-- LIQUID -- copy (PS x s l) = unsafeCreate l $ \p -> withForeignPtr x $ \f ->
-- LIQUID --     memcpy p (f `plusPtr` s) (fromIntegral l)
-- LIQUID -- 
-- LIQUID -- -- ---------------------------------------------------------------------
-- LIQUID -- -- line IO
-- LIQUID -- 
-- LIQUID -- -- | Read a line from stdin.
-- LIQUID -- getLine :: IO ByteString
-- LIQUID -- getLine = hGetLine stdin
-- LIQUID -- 
-- LIQUID -- {-
-- LIQUID -- -- | Lazily construct a list of lines of ByteStrings. This will be much
-- LIQUID -- -- better on memory consumption than using 'hGetContents >>= lines'
-- LIQUID -- -- If you're considering this, a better choice might be to use
-- LIQUID -- -- Data.ByteString.Lazy
-- LIQUID -- hGetLines :: Handle -> IO [ByteString]
-- LIQUID -- hGetLines h = go
-- LIQUID --     where
-- LIQUID --         go = unsafeInterleaveIO $ do
-- LIQUID --                 e <- hIsEOF h
-- LIQUID --                 if e
-- LIQUID --                   then return []
-- LIQUID --                   else do
-- LIQUID --                 x  <- hGetLine h
-- LIQUID --                 xs <- go
-- LIQUID --                 return (x:xs)
-- LIQUID -- -}
-- LIQUID -- 
-- LIQUID -- -- | Read a line from a handle
-- LIQUID -- 
-- LIQUID -- hGetLine :: Handle -> IO ByteString
-- LIQUID -- #if !defined(__GLASGOW_HASKELL__)
-- LIQUID -- hGetLine h = System.IO.hGetLine h >>= return . pack . P.map c2w
-- LIQUID -- #else
-- LIQUID -- hGetLine h = wantReadableHandleLIQUID "Data.ByteString.hGetLine" h $ \ handle_ -> do
-- LIQUID --     case haBufferMode handle_ of
-- LIQUID --        NoBuffering -> error "no buffering"
-- LIQUID --        _other      -> hGetLineBuffered handle_
-- LIQUID -- 
-- LIQUID --  where
-- LIQUID --     hGetLineBuffered handle_ = do
-- LIQUID --         let ref = haCharBuffer handle_
-- LIQUID --         buf <- readIORef ref
-- LIQUID --         hGetLineBufferedLoop handle_ ref buf 0 []
-- LIQUID -- 
-- LIQUID --     hGetLineBufferedLoop handle_ ref
-- LIQUID --             buf@Buffer{ bufL=r, bufR=w, bufRaw=raw } len xss =
-- LIQUID --         len `seq` do
-- LIQUID --         off <- findEOL r w raw
-- LIQUID --         let new_len = len + off - r
-- LIQUID --         xs <- mkPS raw r off
-- LIQUID -- 
-- LIQUID --       -- if eol == True, then off is the offset of the '\n'
-- LIQUID --       -- otherwise off == w and the buffer is now empty.
-- LIQUID --         if off /= w
-- LIQUID --             then do if (w == off + 1)
-- LIQUID --                             then writeIORef ref buf{ bufL=0, bufR=0 }
-- LIQUID --                             else writeIORef ref buf{ bufL = off + 1 }
-- LIQUID --                     mkBigPS new_len (xs:xss)
-- LIQUID --             else do
-- LIQUID --                  maybe_buf <- maybeFillReadBuffer ({- LIQUID COMPAT: haFD -} handle_) True ({- LIQUID COMPAT: haIsStream -} handle_)
-- LIQUID --                                     buf{ bufR=0, bufL=0 }
-- LIQUID --                  case maybe_buf of
-- LIQUID --                     -- Nothing indicates we caught an EOF, and we may have a
-- LIQUID --                     -- partial line to return.
-- LIQUID --                     Nothing -> do
-- LIQUID --                          writeIORef ref buf{ bufL=0, bufR=0 }
-- LIQUID --                          if new_len > 0
-- LIQUID --                             then mkBigPS new_len (xs:xss)
-- LIQUID --                             else error "LIQUIDCOMPAT" -- ioe_EOF
-- LIQUID --                     Just new_buf ->
-- LIQUID --                          hGetLineBufferedLoop handle_ ref new_buf new_len (xs:xss)
-- LIQUID -- 
-- LIQUID --     -- find the end-of-line character, if there is one
-- LIQUID --     findEOL r w raw
-- LIQUID --         | r == w = return w
-- LIQUID --         | otherwise =  do
-- LIQUID --             (c,r') <- readCharFromBuffer raw r
-- LIQUID --             if c == '\n'
-- LIQUID --                 then return r -- NB. not r': don't include the '\n'
-- LIQUID --                 else findEOL r' w raw
-- LIQUID -- 
-- LIQUID --     -- LIQUID COMPAT
-- LIQUID --     maybeFillReadBuffer fd is_line is_stream buf = return Nothing
-- LIQUID --     -- maybeFillReadBuffer fd is_line is_stream buf = catch
-- LIQUID --     --     (do buf' <- fillReadBuffer fd is_line is_stream buf
-- LIQUID --     --         return (Just buf'))
-- LIQUID --     --     (\e -> if isEOFError e then return Nothing else ioError e)
-- LIQUID -- 
-- LIQUID -- -- TODO, rewrite to use normal memcpy
-- LIQUID -- mkPS :: RawBuffer Char -> Int -> Int -> IO ByteString
-- LIQUID -- mkPS buf start end =
-- LIQUID --     let len = end - start
-- LIQUID --     in create len $ \p -> do
-- LIQUID --         memcpy_ptr_baoff p buf (fromIntegral start) ({- LIQUID fromIntegral-} intCSize len)
-- LIQUID --         return ()
-- LIQUID -- 
-- LIQUID -- 
-- LIQUID -- 
-- LIQUID -- mkBigPS :: Int -> [ByteString] -> IO ByteString
-- LIQUID -- mkBigPS _ [ps] = return ps
-- LIQUID -- mkBigPS _ pss = return $! concat (P.reverse pss)
-- LIQUID -- 
-- LIQUID -- #endif
-- LIQUID -- 
-- LIQUID -- -- ---------------------------------------------------------------------
-- LIQUID -- -- Block IO
-- LIQUID -- 
-- LIQUID -- -- | Outputs a 'ByteString' to the specified 'Handle'.
-- LIQUID -- hPut :: Handle -> ByteString -> IO ()
-- LIQUID -- hPut _ (PS _  _ 0) = return ()
-- LIQUID -- hPut h (PS ps s l) = withForeignPtr ps $ \p-> hPutBuf h (p `plusPtr` s) l
-- LIQUID -- 
-- LIQUID -- -- | A synonym for @hPut@, for compatibility 
-- LIQUID -- hPutStr :: Handle -> ByteString -> IO ()
-- LIQUID -- hPutStr = hPut
-- LIQUID -- 
-- LIQUID -- -- | Write a ByteString to a handle, appending a newline byte
-- LIQUID -- hPutStrLn :: Handle -> ByteString -> IO ()
-- LIQUID -- hPutStrLn h ps
-- LIQUID --     | length ps < 1024 = hPut h (ps `snoc` 0x0a)
-- LIQUID --     | otherwise        = hPut h ps >> hPut h (singleton (0x0a)) -- don't copy
-- LIQUID -- 
-- LIQUID -- -- | Write a ByteString to stdout
-- LIQUID -- putStr :: ByteString -> IO ()
-- LIQUID -- putStr = hPut stdout
-- LIQUID -- 
-- LIQUID -- -- | Write a ByteString to stdout, appending a newline byte
-- LIQUID -- putStrLn :: ByteString -> IO ()
-- LIQUID -- putStrLn = hPutStrLn stdout
-- LIQUID -- 
-- LIQUID -- -- | Read a 'ByteString' directly from the specified 'Handle'.  This
-- LIQUID -- -- is far more efficient than reading the characters into a 'String'
-- LIQUID -- -- and then using 'pack'.
-- LIQUID -- hGet :: Handle -> Int -> IO ByteString
-- LIQUID -- hGet _ 0 = return empty
-- LIQUID -- hGet h i = createAndTrim i $ \p -> hGetBuf h p i
-- LIQUID -- 
-- LIQUID -- -- | hGetNonBlocking is identical to 'hGet', except that it will never block
-- LIQUID -- -- waiting for data to become available, instead it returns only whatever data
-- LIQUID -- -- is available.
-- LIQUID -- hGetNonBlocking :: Handle -> Int -> IO ByteString
-- LIQUID -- #if defined(__GLASGOW_HASKELL__)
-- LIQUID -- hGetNonBlocking _ 0 = return empty
-- LIQUID -- hGetNonBlocking h i = createAndTrim i $ \p -> hGetBufNonBlocking h p i
-- LIQUID -- #else
-- LIQUID -- hGetNonBlocking = hGet
-- LIQUID -- #endif
-- LIQUID -- 
-- LIQUID -- -- | Read entire handle contents into a 'ByteString'.
-- LIQUID -- -- This function reads chunks at a time, doubling the chunksize on each
-- LIQUID -- -- read. The final buffer is then realloced to the appropriate size. For
-- LIQUID -- -- files > half of available memory, this may lead to memory exhaustion.
-- LIQUID -- -- Consider using 'readFile' in this case.
-- LIQUID -- --
-- LIQUID -- -- As with 'hGet', the string representation in the file is assumed to
-- LIQUID -- -- be ISO-8859-1.
-- LIQUID -- --
-- LIQUID -- hGetContents :: Handle -> IO ByteString
-- LIQUID -- hGetContents h = do
-- LIQUID --     let start_size = 1024
-- LIQUID --     p <- mallocBytes start_size
-- LIQUID --     i <- hGetBuf h p start_size
-- LIQUID --     if i < start_size
-- LIQUID --         then do p' <- reallocBytes p i
-- LIQUID --                 fp <- newForeignPtr finalizerFree p'
-- LIQUID --                 return $! PS fp 0 i
-- LIQUID --         else f p start_size
-- LIQUID --     where
-- LIQUID --         f p s = do
-- LIQUID --             let s' = 2 * s
-- LIQUID --             p' <- reallocBytes p s'
-- LIQUID --             i  <- hGetBuf h (p' `plusPtr` s) s
-- LIQUID --             if i < s
-- LIQUID --                 then do let i' = s + i
-- LIQUID --                         p'' <- reallocBytes p' i'
-- LIQUID --                         fp  <- newForeignPtr finalizerFree p''
-- LIQUID --                         return $! PS fp 0 i'
-- LIQUID --                 else f p' s'
-- LIQUID -- 
-- LIQUID -- -- | getContents. Equivalent to hGetContents stdin
-- LIQUID -- getContents :: IO ByteString
-- LIQUID -- getContents = hGetContents stdin
-- LIQUID -- 
-- LIQUID -- -- | The interact function takes a function of type @ByteString -> ByteString@
-- LIQUID -- -- as its argument. The entire input from the standard input device is passed
-- LIQUID -- -- to this function as its argument, and the resulting string is output on the
-- LIQUID -- -- standard output device. It's great for writing one line programs!
-- LIQUID -- interact :: (ByteString -> ByteString) -> IO ()
-- LIQUID -- interact transformer = putStr . transformer =<< getContents
-- LIQUID -- 
-- LIQUID -- -- | Read an entire file strictly into a 'ByteString'.  This is far more
-- LIQUID -- -- efficient than reading the characters into a 'String' and then using
-- LIQUID -- -- 'pack'.  It also may be more efficient than opening the file and
-- LIQUID -- -- reading it using hGet. Files are read using 'binary mode' on Windows,
-- LIQUID -- -- for 'text mode' use the Char8 version of this function.
-- LIQUID -- readFile :: FilePath -> IO ByteString
-- LIQUID -- readFile f = bracket (openBinaryFile f ReadMode) hClose
-- LIQUID --     (\h -> hFileSize h >>= hGet h . fromIntegral)
-- LIQUID -- 
-- LIQUID -- -- | Write a 'ByteString' to a file.
-- LIQUID -- writeFile :: FilePath -> ByteString -> IO ()
-- LIQUID -- writeFile f txt = bracket (openBinaryFile f WriteMode) hClose
-- LIQUID --     (\h -> hPut h txt)
-- LIQUID -- 
-- LIQUID -- -- | Append a 'ByteString' to a file.
-- LIQUID -- appendFile :: FilePath -> ByteString -> IO ()
-- LIQUID -- appendFile f txt = bracket (openBinaryFile f AppendMode) hClose
-- LIQUID --     (\h -> hPut h txt)
-- LIQUID -- 
-- LIQUID -- {-
-- LIQUID -- --
-- LIQUID -- -- Disable until we can move it into a portable .hsc file
-- LIQUID -- --
-- LIQUID -- 
-- LIQUID -- -- | Like readFile, this reads an entire file directly into a
-- LIQUID -- -- 'ByteString', but it is even more efficient.  It involves directly
-- LIQUID -- -- mapping the file to memory.  This has the advantage that the contents
-- LIQUID -- -- of the file never need to be copied.  Also, under memory pressure the
-- LIQUID -- -- page may simply be discarded, while in the case of readFile it would
-- LIQUID -- -- need to be written to swap.  If you read many small files, mmapFile
-- LIQUID -- -- will be less memory-efficient than readFile, since each mmapFile
-- LIQUID -- -- takes up a separate page of memory.  Also, you can run into bus
-- LIQUID -- -- errors if the file is modified.  As with 'readFile', the string
-- LIQUID -- -- representation in the file is assumed to be ISO-8859-1.
-- LIQUID -- --
-- LIQUID -- -- On systems without mmap, this is the same as a readFile.
-- LIQUID -- --
-- LIQUID -- mmapFile :: FilePath -> IO ByteString
-- LIQUID -- mmapFile f = mmap f >>= \(fp,l) -> return $! PS fp 0 l
-- LIQUID -- 
-- LIQUID -- mmap :: FilePath -> IO (ForeignPtr Word8, Int)
-- LIQUID -- mmap f = do
-- LIQUID --     h <- openBinaryFile f ReadMode
-- LIQUID --     l <- fromIntegral `fmap` hFileSize h
-- LIQUID --     -- Don't bother mmaping small files because each mmapped file takes up
-- LIQUID --     -- at least one full VM block.
-- LIQUID --     if l < mmap_limit
-- LIQUID --        then do thefp <- mallocByteString l
-- LIQUID --                withForeignPtr thefp $ \p-> hGetBuf h p l
-- LIQUID --                hClose h
-- LIQUID --                return (thefp, l)
-- LIQUID --        else do
-- LIQUID --                -- unix only :(
-- LIQUID --                fd <- fromIntegral `fmap` handleToFd h
-- LIQUID --                p  <- my_mmap l fd
-- LIQUID --                fp <- if p == nullPtr
-- LIQUID --                      then do thefp <- mallocByteString l
-- LIQUID --                              withForeignPtr thefp $ \p' -> hGetBuf h p' l
-- LIQUID --                              return thefp
-- LIQUID --                      else do
-- LIQUID --                           -- The munmap leads to crashes on OpenBSD.
-- LIQUID --                           -- maybe there's a use after unmap in there somewhere?
-- LIQUID --                           -- Bulat suggests adding the hClose to the
-- LIQUID --                           -- finalizer, excellent idea.
-- LIQUID -- #if !defined(__OpenBSD__)
-- LIQUID --                              let unmap = c_munmap p l >> return ()
-- LIQUID -- #else
-- LIQUID --                              let unmap = return ()
-- LIQUID -- #endif
-- LIQUID --                              fp <- newForeignPtr p unmap
-- LIQUID --                              return fp
-- LIQUID --                c_close fd
-- LIQUID --                hClose h
-- LIQUID --                return (fp, l)
-- LIQUID --     where mmap_limit = 16*1024
-- LIQUID -- -}
-- LIQUID -- 
-- ---------------------------------------------------------------------
-- Internal utilities

-- | 'findIndexOrEnd' is a variant of findIndex, that returns the length
-- of the string if no element is found, rather than Nothing.
-- LIQUID -- findIndexOrEnd :: (Word8 -> Bool) -> ByteString -> Int
-- LIQUID -- findIndexOrEnd k (PS x s l) = inlinePerformIO $ withForeignPtr x $ \f -> go (f `plusPtr` s) 0
-- LIQUID --   where
-- LIQUID --     STRICT2(go)
-- LIQUID --     go ptr n | n >= l    = return l
-- LIQUID --              | otherwise = do w <- peek ptr
-- LIQUID --                               if k w
-- LIQUID --                                 then return n
-- LIQUID --                                 else go (ptr `plusPtr` 1) (n+1)
-- LIQUID -- {-# INLINE findIndexOrEnd #-}

-- | Perform an operation with a temporary ByteString
withPtr :: ForeignPtr a -> (Ptr a -> IO b) -> b
withPtr fp io = inlinePerformIO (withForeignPtr fp io)
{-# INLINE withPtr #-}

-- Common up near identical calls to `error' to reduce the number
-- constant strings created when compiled:
{-@ errorEmptyList :: {v:String | false} -> a @-}
errorEmptyList :: String -> a
errorEmptyList fun = moduleError fun "empty ByteString"
{-# NOINLINE errorEmptyList #-}

{-@ moduleError :: String -> String -> a @-}
moduleError :: String -> String -> a
moduleError fun msg = error ("Data.ByteString." ++ fun ++ ':':' ':msg)
{-# NOINLINE moduleError #-}

-- LIQUID -- -- Find from the end of the string using predicate
-- LIQUID -- findFromEndUntil :: (Word8 -> Bool) -> ByteString -> Int
-- LIQUID -- STRICT2(findFromEndUntil)
-- LIQUID -- findFromEndUntil f ps@(PS x s l) =
-- LIQUID --     if null ps then 0
-- LIQUID --     else if f (last ps) then l
-- LIQUID --          else findFromEndUntil f (PS x s (l-1))


