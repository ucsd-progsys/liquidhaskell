{-# OPTIONS_GHC -cpp -fglasgow-exts -fno-warn-orphans -fno-warn-incomplete-patterns #-}

-- #prune

-- |
-- Module      : Data.ByteString.Lazy
-- Copyright   : (c) Don Stewart 2006
--               (c) Duncan Coutts 2006
-- License     : BSD-style
--
-- Maintainer  : dons@galois.com
-- Stability   : experimental
-- Portability : portable
-- 
-- A time and space-efficient implementation of lazy byte vectors
-- using lists of packed 'Word8' arrays, suitable for high performance
-- use, both in terms of large data quantities, or high speed
-- requirements. Byte vectors are encoded as lazy lists of strict 'Word8'
-- arrays of bytes. They provide a means to manipulate large byte vectors
-- without requiring the entire vector be resident in memory.
--
-- Some operations, such as concat, append, reverse and cons, have
-- better complexity than their "Data.ByteString" equivalents, due to
-- optimisations resulting from the list spine structure. And for other
-- operations lazy ByteStrings are usually within a few percent of
-- strict ones, but with better heap usage. For data larger than the
-- available memory, or if you have tight memory constraints, this
-- module will be the only option. The default chunk size is 64k, which
-- should be good in most circumstances. For people with large L2
-- caches, you may want to increase this to fit your cache.
--
-- This module is intended to be imported @qualified@, to avoid name
-- clashes with "Prelude" functions.  eg.
--
-- > import qualified Data.ByteString.Lazy as B
--
-- Original GHC implementation by Bryan O\'Sullivan.
-- Rewritten to use 'Data.Array.Unboxed.UArray' by Simon Marlow.
-- Rewritten to support slices and use 'Foreign.ForeignPtr.ForeignPtr'
-- by David Roundy.
-- Polished and extended by Don Stewart.
-- Lazy variant by Duncan Coutts and Don Stewart.
--

module Data.ByteString.Lazy (

        -- * The @ByteString@ type
        ByteString,             -- instances: Eq, Ord, Show, Read, Data, Typeable

        -- * Introducing and eliminating 'ByteString's
        empty,                  -- :: ByteString
        singleton,              -- :: Word8   -> ByteString
        pack,                   -- :: [Word8] -> ByteString
        unpack,                 -- :: ByteString -> [Word8]
        fromChunks,             -- :: [Strict.ByteString] -> ByteString
        toChunks,               -- :: ByteString -> [Strict.ByteString]

        -- * Basic interface
        cons,                   -- :: Word8 -> ByteString -> ByteString
        cons',                  -- :: Word8 -> ByteString -> ByteString
        snoc,                   -- :: ByteString -> Word8 -> ByteString
        append,                 -- :: ByteString -> ByteString -> ByteString
        head,                   -- :: ByteString -> Word8
        uncons,                 -- :: ByteString -> Maybe (Word8, ByteString)
        last,                   -- :: ByteString -> Word8
        tail,                   -- :: ByteString -> ByteString
        init,                   -- :: ByteString -> ByteString
        null,                   -- :: ByteString -> Bool
        length,                 -- :: ByteString -> Int64

        -- * Transforming ByteStrings
        map,                    -- :: (Word8 -> Word8) -> ByteString -> ByteString
        reverse,                -- :: ByteString -> ByteString
        intersperse,            -- :: Word8 -> ByteString -> ByteString
        intercalate,            -- :: ByteString -> [ByteString] -> ByteString
        transpose,              -- :: [ByteString] -> [ByteString]

        -- * Reducing 'ByteString's (folds)
        foldl,                  -- :: (a -> Word8 -> a) -> a -> ByteString -> a
        foldl',                 -- :: (a -> Word8 -> a) -> a -> ByteString -> a
        foldl1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
        foldl1',                -- :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
        foldr,                  -- :: (Word8 -> a -> a) -> a -> ByteString -> a
        foldr1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8

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
--        scanl1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
--        scanr,                  -- :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
--        scanr1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString

        -- ** Accumulating maps
        mapAccumL,              -- :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
        mapAccumR,              -- :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
        mapIndexed,             -- :: (Int64 -> Word8 -> Word8) -> ByteString -> ByteString

--LIQUID        -- ** Infinite ByteStrings
--LIQUID        repeat,                 -- :: Word8 -> ByteString
--LIQUID        replicate,              -- :: Int64 -> Word8 -> ByteString
--LIQUID        cycle,                  -- :: ByteString -> ByteString
--LIQUID        iterate,                -- :: (Word8 -> Word8) -> Word8 -> ByteString
--LIQUID
--LIQUID        -- ** Unfolding ByteStrings
--LIQUID        unfoldr,                -- :: (a -> Maybe (Word8, a)) -> a -> ByteString
--LIQUID
       -- * Substrings

       -- ** Breaking strings
       take,                   -- :: Int64 -> ByteString -> ByteString
       drop,                   -- :: Int64 -> ByteString -> ByteString
       splitAt,                -- :: Int64 -> ByteString -> (ByteString, ByteString)
       takeWhile,              -- :: (Word8 -> Bool) -> ByteString -> ByteString
       dropWhile,              -- :: (Word8 -> Bool) -> ByteString -> ByteString
       span,                   -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
       break,                  -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
--LIQUID        group,                  -- :: ByteString -> [ByteString]
--LIQUID        groupBy,                -- :: (Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]
--LIQUID        inits,                  -- :: ByteString -> [ByteString]
--LIQUID        tails,                  -- :: ByteString -> [ByteString]

       -- ** Breaking into many substrings
--LIQUID        split,                  -- :: Word8 -> ByteString -> [ByteString]
--LIQUID        splitWith,              -- :: (Word8 -> Bool) -> ByteString -> [ByteString]

       -- * Predicates
       isPrefixOf,             -- :: ByteString -> ByteString -> Bool
       isSuffixOf,             -- :: ByteString -> ByteString -> Bool
--LIQUID--        isInfixOf,              -- :: ByteString -> ByteString -> Bool
--LIQUID
--LIQUID        -- ** Search for arbitrary substrings
--LIQUID--        isSubstringOf,          -- :: ByteString -> ByteString -> Bool
--LIQUID--        findSubstring,          -- :: ByteString -> ByteString -> Maybe Int
--LIQUID--        findSubstrings,         -- :: ByteString -> ByteString -> [Int]
--LIQUID
--LIQUID        -- * Searching ByteStrings
--LIQUID
--LIQUID        -- ** Searching by equality
--LIQUID        elem,                   -- :: Word8 -> ByteString -> Bool
--LIQUID        notElem,                -- :: Word8 -> ByteString -> Bool
--LIQUID
--LIQUID        -- ** Searching with a predicate
--LIQUID        find,                   -- :: (Word8 -> Bool) -> ByteString -> Maybe Word8
--LIQUID        filter,                 -- :: (Word8 -> Bool) -> ByteString -> ByteString
--LIQUID        partition,              -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
--LIQUID
--LIQUID        -- * Indexing ByteStrings
--LIQUID        index,                  -- :: ByteString -> Int64 -> Word8
--LIQUID        elemIndex,              -- :: Word8 -> ByteString -> Maybe Int64
--LIQUID        elemIndices,            -- :: Word8 -> ByteString -> [Int64]
--LIQUID        findIndex,              -- :: (Word8 -> Bool) -> ByteString -> Maybe Int64
--LIQUID        findIndices,            -- :: (Word8 -> Bool) -> ByteString -> [Int64]
--LIQUID        count,                  -- :: Word8 -> ByteString -> Int64
--LIQUID
--LIQUID        -- * Zipping and unzipping ByteStrings
--LIQUID        zip,                    -- :: ByteString -> ByteString -> [(Word8,Word8)]
--LIQUID        zipWith,                -- :: (Word8 -> Word8 -> c) -> ByteString -> ByteString -> [c]
--LIQUID        unzip,                  -- :: [(Word8,Word8)] -> (ByteString,ByteString)
--LIQUID
--LIQUID        -- * Ordered ByteStrings
--LIQUID--        sort,                   -- :: ByteString -> ByteString
--LIQUID
--LIQUID        -- * Low level conversions
--LIQUID        -- ** Copying ByteStrings
--LIQUID        copy,                   -- :: ByteString -> ByteString
--LIQUID--        defrag,                -- :: ByteString -> ByteString
--LIQUID
--LIQUID        -- * I\/O with 'ByteString's
--LIQUID
--LIQUID        -- ** Standard input and output
--LIQUID        getContents,            -- :: IO ByteString
--LIQUID        putStr,                 -- :: ByteString -> IO ()
--LIQUID        putStrLn,               -- :: ByteString -> IO ()
--LIQUID        interact,               -- :: (ByteString -> ByteString) -> IO ()
--LIQUID
--LIQUID        -- ** Files
--LIQUID        readFile,               -- :: FilePath -> IO ByteString
--LIQUID        writeFile,              -- :: FilePath -> ByteString -> IO ()
--LIQUID        appendFile,             -- :: FilePath -> ByteString -> IO ()
--LIQUID
--LIQUID        -- ** I\/O with Handles
--LIQUID        hGetContents,           -- :: Handle -> IO ByteString
--LIQUID        hGet,                   -- :: Handle -> Int -> IO ByteString
--LIQUID        hGetNonBlocking,        -- :: Handle -> Int -> IO ByteString
--LIQUID        hPut,                   -- :: Handle -> ByteString -> IO ()
--LIQUID        hPutStr,                -- :: Handle -> ByteString -> IO ()
--LIQUID
--LIQUID--      hGetN,                  -- :: Int -> Handle -> Int -> IO ByteString
--LIQUID--      hGetContentsN,          -- :: Int -> Handle -> IO ByteString
--LIQUID--      hGetNonBlockingN,       -- :: Int -> Handle -> IO ByteString
--LIQUID
--LIQUID        -- undocumented deprecated things:
--LIQUID        join                    -- :: ByteString -> [ByteString] -> ByteString

  ) where

import qualified Prelude
import Prelude hiding
    (reverse,head,tail,last,init,null,length,map,lines,foldl,foldr,unlines
    ,concat,any,take,drop,splitAt,takeWhile,dropWhile,span,break,elem,filter,maximum
    ,minimum,all,concatMap,foldl1,foldr1,scanl, scanl1, scanr, scanr1
    ,repeat, cycle, interact, iterate,readFile,writeFile,appendFile,replicate
    ,getContents,getLine,putStr,putStrLn ,zip,zipWith,unzip,notElem)

import qualified Data.List              as L  -- L for list/lazy
import qualified Data.ByteString        as S  -- S for strict (hmm...)
import qualified Data.ByteString.Internal as S
import qualified Data.ByteString.Unsafe as S
import Data.ByteString.Lazy.Internal
import qualified Data.ByteString.Fusion as F

import Data.Monoid              (Monoid(..))

import Data.Word                (Word8)
import Data.Int                 (Int64)
import System.IO                (Handle,stdin,stdout,openBinaryFile,IOMode(..)
                                ,hClose,hWaitForInput,hIsEOF)
import System.IO.Unsafe
#ifndef __NHC__
import Control.Exception        (bracket)
#else
import IO		        (bracket)
#endif

import Foreign.ForeignPtr       (withForeignPtr)
import Foreign.Ptr
import Foreign.Storable

--LIQUID
import Data.ByteString.Fusion   (PairS(..))
import Data.Int
import Data.Word                (Word, Word8, Word16, Word32, Word64)
import qualified Data.ByteString.Internal
import Foreign.ForeignPtr       (ForeignPtr)
import qualified Foreign.C.Types

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
    where compare = cmp

instance Monoid ByteString where
    mempty  = empty
    mappend = append
    mconcat = concat

{-@ eq :: LByteString -> LByteString -> Bool @-}
eq :: ByteString -> ByteString -> Bool
eq Empty Empty = True
eq Empty _     = False
eq _     Empty = False
eq (Chunk a as) (Chunk b bs) =
  case compare (S.length a) (S.length b) of
    LT -> a == (S.take (S.length a) b) && eq as (Chunk (S.drop (S.length a) b) bs)
    EQ -> a == b                       && eq as bs
    GT -> (S.take (S.length b) a) == b && eq (Chunk (S.drop (S.length b) a) as) bs

{-@ cmp :: LByteString -> LByteString -> Ordering @-}
cmp :: ByteString -> ByteString -> Ordering
cmp Empty Empty = EQ
cmp Empty _     = LT
cmp _     Empty = GT
cmp (Chunk a as) (Chunk b bs) =
  case compare (S.length a) (S.length b) of
    LT -> case compare a (S.take (S.length a) b) of
            EQ     -> cmp as (Chunk (S.drop (S.length a) b) bs)
            result -> result
    EQ -> case compare a b of
            EQ     -> cmp as bs
            result -> result
    GT -> case compare (S.take (S.length b) a) b of
            EQ     -> cmp (Chunk (S.drop (S.length b) a) as) bs
            result -> result

-- -----------------------------------------------------------------------------
-- Introducing and eliminating 'ByteString's

-- | /O(1)/ The empty 'ByteString'
{-@ empty :: {v:LByteString | (lbLength v) = 0} @-}
empty :: ByteString
empty = Empty
{-# INLINE empty #-}

-- | /O(1)/ Convert a 'Word8' into a 'ByteString'
{-@ singleton :: Word8 -> {v:LByteString | (lbLength v) = 1} @-}
singleton :: Word8 -> ByteString
singleton w = Chunk (S.singleton w) Empty
{-# INLINE singleton #-}

-- | /O(n)/ Convert a '[Word8]' into a 'ByteString'. 
pack :: [Word8] -> ByteString
pack ws = L.foldr (Chunk . S.pack) Empty (chunks defaultChunkSize ws)
  where
    chunks :: Int -> [a] -> [[a]]
    chunks _    [] = []
    chunks size xs = case L.splitAt size xs of
                      (xs', xs'') -> xs' : chunks size xs''

-- | /O(n)/ Converts a 'ByteString' to a '[Word8]'.
unpack :: ByteString -> [Word8]
unpack cs = L.concatMap S.unpack (toChunks cs)
--TODO: we can do better here by integrating the concat with the unpack

-- | /O(c)/ Convert a list of strict 'ByteString' into a lazy 'ByteString'
fromChunks :: [S.ByteString] -> ByteString
fromChunks cs = L.foldr chunk Empty cs

-- | /O(n)/ Convert a lazy 'ByteString' into a list of strict 'ByteString'
toChunks :: ByteString -> [S.ByteString]
--LIQUID toChunks cs = foldrChunks (:) [] cs
toChunks cs = foldrChunks (const (:)) [] cs

------------------------------------------------------------------------

{-
-- | /O(n)/ Convert a '[a]' into a 'ByteString' using some
-- conversion function
packWith :: (a -> Word8) -> [a] -> ByteString
packWith k str = LPS $ L.map (P.packWith k) (chunk defaultChunkSize str)
{-# INLINE packWith #-}
{-# SPECIALIZE packWith :: (Char -> Word8) -> [Char] -> ByteString #-}

-- | /O(n)/ Converts a 'ByteString' to a '[a]', using a conversion function.
unpackWith :: (Word8 -> a) -> ByteString -> [a]
unpackWith k (LPS ss) = L.concatMap (S.unpackWith k) ss
{-# INLINE unpackWith #-}
{-# SPECIALIZE unpackWith :: (Word8 -> Char) -> ByteString -> [Char] #-}
-}

-- ---------------------------------------------------------------------
-- Basic interface

-- | /O(1)/ Test whether a ByteString is empty.
{-@ null :: b:LByteString -> {v:Bool | ((Prop v) <=> ((lbLength b) = 0))} @-}
null :: ByteString -> Bool
null Empty = True
null _     = False
{-# INLINE null #-}

-- | /O(n\/c)/ 'length' returns the length of a ByteString as an 'Int64'
{-@ length :: b:LByteString -> {v:Int64 | v = (lbLength b)} @-}
length :: ByteString -> Int64
--LIQUID length cs = foldlChunks (\n c -> n + fromIntegral (S.length c)) 0 cs
length cs = foldrChunks (\_ c n -> n + fromIntegral (S.length c)) 0 cs
{-# INLINE length #-}

-- | /O(1)/ 'cons' is analogous to '(:)' for lists.
--
{-@ cons :: Word8 -> b:LByteString -> {v:LByteString | (lbLength v) = ((lbLength b) + 1)}
  @-}
cons :: Word8 -> ByteString -> ByteString
cons c cs = Chunk (S.singleton c) cs
{-# INLINE cons #-}

-- | /O(1)/ Unlike 'cons', 'cons\'' is
-- strict in the ByteString that we are consing onto. More precisely, it forces
-- the head and the first chunk. It does this because, for space efficiency, it
-- may coalesce the new byte onto the first \'chunk\' rather than starting a
-- new \'chunk\'.
--
-- So that means you can't use a lazy recursive contruction like this:
--
-- > let xs = cons\' c xs in xs
--
-- You can however use 'cons', as well as 'repeat' and 'cycle', to build
-- infinite lazy ByteStrings.
--
{-@ cons' :: Word8 -> b:LByteString -> {v:LByteString | (lbLength v) = ((lbLength b) + 1)} @-}
cons' :: Word8 -> ByteString -> ByteString
cons' w (Chunk c cs) | S.length c < 16 = Chunk (S.cons w c) cs
cons' w cs                             = Chunk (S.singleton w) cs
{-# INLINE cons' #-}

-- | /O(n\/c)/ Append a byte to the end of a 'ByteString'
{-@ snoc :: b:LByteString -> Word8 -> {v:LByteString | (lbLength v) = ((lbLength b) + 1)} @-}
snoc :: ByteString -> Word8 -> ByteString
--LIQUID snoc cs w = foldrChunks Chunk (singleton w) cs
snoc cs w = foldrChunks (const Chunk) (singleton w) cs
{-# INLINE snoc #-}

-- | /O(1)/ Extract the first element of a ByteString, which must be non-empty.
{-@ head :: LByteStringNE -> Word8 @-}
head :: ByteString -> Word8
head Empty       = errorEmptyList "head"
head (Chunk c _) = S.unsafeHead c
{-# INLINE head #-}

-- | /O(1)/ Extract the head and tail of a ByteString, returning Nothing
-- if it is empty.
{-@ uncons :: b:LByteString
           -> Maybe (Word8, {v:LByteString | (lbLength v) = (lbLength b) - 1})
  @-}
uncons :: ByteString -> Maybe (Word8, ByteString)
uncons Empty = Nothing
uncons (Chunk c cs)
    = Just (S.unsafeHead c,
            if S.length c == 1 then cs else Chunk (S.unsafeTail c) cs)
{-# INLINE uncons #-}

-- | /O(1)/ Extract the elements after the head of a ByteString, which must be
-- non-empty.
{-@ tail :: b:LByteStringNE -> {v:LByteString | (lbLength v) = ((lbLength b) - 1)} @-}
tail :: ByteString -> ByteString
tail Empty          = errorEmptyList "tail"
tail (Chunk c cs)
  | S.length c == 1 = cs
  | otherwise       = Chunk (S.unsafeTail c) cs
{-# INLINE tail #-}

-- | /O(n\/c)/ Extract the last element of a ByteString, which must be finite
-- and non-empty.
{-@ last :: LByteStringNE -> Word8 @-}
last :: ByteString -> Word8
last Empty          = errorEmptyList "last"
last (Chunk c0 cs0) = go c0 cs0
  where go c Empty        = S.last c
        go _ (Chunk c cs) = go c cs
-- XXX Don't inline this. Something breaks with 6.8.2 (haven't investigated yet)

{-@ qualif LBLenAcc(v:Data.ByteString.Lazy.Internal.ByteString,
                    sb:Data.ByteString.Internal.ByteString,
                    lb:Data.ByteString.Lazy.Internal.ByteString):
        (lbLength v) = ((bLength sb) + (lbLength lb) - 1)
  @-}

-- | /O(n\/c)/ Return all the elements of a 'ByteString' except the last one.
{-@ init :: b:LByteStringNE -> {v:LByteString | (lbLength v) = ((lbLength b) - 1)} @-}
init :: ByteString -> ByteString
init Empty          = errorEmptyList "init"
init (Chunk c0 cs0) = go c0 cs0
  where go c Empty | S.length c == 1 = Empty
                   | otherwise       = Chunk (S.init c) Empty
        go c (Chunk c' cs)           = Chunk c (go c' cs)

-- | /O(n\/c)/ Append two ByteStrings
{-@ append :: b1:LByteString -> b2:LByteString
           -> {v:LByteString | (lbLength v) = (lbLength b1) + (lbLength b2)}
  @-}
append :: ByteString -> ByteString -> ByteString
--LIQUID append xs ys = foldrChunks Chunk ys xs
append xs ys = foldrChunks (const Chunk) ys xs
{-# INLINE append #-}

-- ---------------------------------------------------------------------
-- Transformations

-- | /O(n)/ 'map' @f xs@ is the ByteString obtained by applying @f@ to each
-- element of @xs@.
{-@ map :: (Word8 -> Word8) -> b:LByteString -> (LByteStringSZ b) @-}
map :: (Word8 -> Word8) -> ByteString -> ByteString
map f s = go s
    where
        go Empty        = Empty
        go (Chunk x xs) = Chunk y ys
            where
                y  = S.map f x
                ys = go xs
{-# INLINE map #-}

-- | /O(n)/ 'reverse' @xs@ returns the elements of @xs@ in reverse order.
{-@ reverse :: b:LByteString -> (LByteStringSZ b) @-}
reverse :: ByteString -> ByteString
reverse cs0 = rev Empty cs0
  where rev a Empty        = a
        rev a (Chunk c cs) = rev (Chunk (S.reverse c) a) cs
{-# INLINE reverse #-}

-- | The 'intersperse' function takes a 'Word8' and a 'ByteString' and
-- \`intersperses\' that byte between the elements of the 'ByteString'.
-- It is analogous to the intersperse function on Lists.
{-@ intersperse :: Word8 -> b:LByteString
                -> {v:LByteString |
                     (((lbLength b) >= 2) ? ((lbLength v) = (2 * (lbLength b)) - 1)
                                          : ((lbLength v) = (lbLength b))) }
  @-}
intersperse :: Word8 -> ByteString -> ByteString
intersperse _ Empty        = Empty
intersperse w (Chunk c cs) = Chunk (S.intersperse w c)
                                   --LIQUID (foldrChunks (Chunk . intersperse') Empty cs)
                                   (foldrChunks (const $ Chunk . intersperse') Empty cs)
  where intersperse' :: S.ByteString -> S.ByteString
        intersperse' (S.PS fp o l) =
          S.unsafeCreate {-LIQUID (2*l)-} (l+l) $ \p' -> withForeignPtr fp $ \p -> do
            poke p' w
            S.c_intersperse (p' `plusPtr` 1) (p `plusPtr` o) (fromIntegral l) w

-- | The 'transpose' function transposes the rows and columns of its
-- 'ByteString' argument.
transpose :: [ByteString] -> [ByteString]
transpose css = L.map (\ss -> Chunk (S.pack ss) Empty)
                      (L.transpose (L.map unpack css))
--TODO: make this fast

-- ---------------------------------------------------------------------
-- Reducing 'ByteString's

-- | 'foldl', applied to a binary operator, a starting value (typically
-- the left-identity of the operator), and a ByteString, reduces the
-- ByteString using the binary operator, from left to right.
foldl :: (a -> Word8 -> a) -> a -> ByteString -> a
foldl f z = go z
  where go a Empty        = a
        go a (Chunk c cs) = go (S.foldl f a c) cs
{-# INLINE foldl #-}

-- | 'foldl\'' is like 'foldl', but strict in the accumulator.
foldl' :: (a -> Word8 -> a) -> a -> ByteString -> a
foldl' f z = go z
  where go a _ | a `seq` False = undefined
        go a Empty        = a
        go a (Chunk c cs) = go (S.foldl f a c) cs
{-# INLINE foldl' #-}

-- | 'foldr', applied to a binary operator, a starting value
-- (typically the right-identity of the operator), and a ByteString,
-- reduces the ByteString using the binary operator, from right to left.
foldr :: (Word8 -> a -> a) -> a -> ByteString -> a
--LIQUID foldr k z cs = foldrChunks (flip (S.foldr k)) z cs
foldr k z cs = foldrChunks (const $ flip (S.foldr k)) z cs
{-# INLINE foldr #-}

-- | 'foldl1' is a variant of 'foldl' that has no starting value
-- argument, and thus must be applied to non-empty 'ByteStrings'.
-- This function is subject to array fusion.
{-@ foldl1 :: (Word8 -> Word8 -> Word8) -> LByteStringNE -> Word8 @-}
foldl1 :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldl1 _ Empty        = errorEmptyList "foldl1"
                        --LIQUID FIXME: S.unsafeTail breaks the lazy
                        --invariant, but since the bytestring is
                        --immediately consumed by foldl it may
                        --actually be safe
foldl1 f (Chunk c cs) = foldl f (S.unsafeHead c) (Chunk (S.unsafeTail c) cs)

-- | 'foldl1\'' is like 'foldl1', but strict in the accumulator.
{-@ foldl1' :: (Word8 -> Word8 -> Word8) -> LByteStringNE -> Word8 @-}
foldl1' :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldl1' _ Empty        = errorEmptyList "foldl1'"
foldl1' f (Chunk c cs) = foldl' f (S.unsafeHead c) (Chunk (S.unsafeTail c) cs)

-- | 'foldr1' is a variant of 'foldr' that has no starting value argument,
-- and thus must be applied to non-empty 'ByteString's
{-@ foldr1 :: (Word8 -> Word8 -> Word8) -> LByteStringNE -> Word8 @-}
foldr1 :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldr1 _ Empty          = errorEmptyList "foldr1"
foldr1 f (Chunk c0 cs0) = go c0 cs0
  where go c Empty         = S.foldr1 f c
        go c (Chunk c' cs) = S.foldr  f (go c' cs) c

-- ---------------------------------------------------------------------
-- Special folds

-- | /O(n)/ Concatenate a list of ByteStrings.
{-@ concat :: bs:[LByteString] -> {v:LByteString | (lbLength v) = (lbLengths bs)} @-}
concat :: [ByteString] -> ByteString
concat css0 = to css0
  where
    go Empty        css = to css
    go (Chunk c cs) css = Chunk c (go cs css)
    to []               = Empty
    to (cs:css)         = go cs css

-- | Map a function over a 'ByteString' and concatenate the results
concatMap :: (Word8 -> ByteString) -> ByteString -> ByteString
concatMap _ Empty        = Empty
concatMap f (Chunk c0 cs0) = to c0 cs0
  where
    go :: ByteString -> S.ByteString -> ByteString -> ByteString
    go Empty        c' cs' = to c' cs'
    go (Chunk c cs) c' cs' = Chunk c (go cs c' cs')

    to :: S.ByteString -> ByteString -> ByteString
    to c cs | S.null c  = case cs of
        Empty          -> Empty
        (Chunk c' cs') -> to c' cs'
            | otherwise = go (f (S.unsafeHead c)) (S.unsafeTail c) cs

-- | /O(n)/ Applied to a predicate and a ByteString, 'any' determines if
-- any element of the 'ByteString' satisfies the predicate.
any :: (Word8 -> Bool) -> ByteString -> Bool
--LIQUID any f cs = foldrChunks (\c rest -> S.any f c || rest) False cs
any f cs = foldrChunks (\_ c rest -> S.any f c || rest) False cs
{-# INLINE any #-}
-- todo fuse

-- | /O(n)/ Applied to a predicate and a 'ByteString', 'all' determines
-- if all elements of the 'ByteString' satisfy the predicate.
all :: (Word8 -> Bool) -> ByteString -> Bool
--LIQUID all f cs = foldrChunks (\c rest -> S.all f c && rest) True cs
all f cs = foldrChunks (\_ c rest -> S.all f c && rest) True cs
{-# INLINE all #-}
-- todo fuse

-- | /O(n)/ 'maximum' returns the maximum value from a 'ByteString'
{-@ maximum :: LByteStringNE -> Word8 @-}
maximum :: ByteString -> Word8
maximum Empty        = errorEmptyList "maximum"
maximum (Chunk c cs) = foldlChunks (\n c' -> n `max` S.maximum c')
                                   (S.maximum c) cs
{-# INLINE maximum #-}

-- | /O(n)/ 'minimum' returns the minimum value from a 'ByteString'
{-@ minimum :: LByteStringNE -> Word8 @-}
minimum :: ByteString -> Word8
minimum Empty        = errorEmptyList "minimum"
minimum (Chunk c cs) = foldlChunks (\n c' -> n `min` S.minimum c')
                                     (S.minimum c) cs
{-# INLINE minimum #-}

-- | The 'mapAccumL' function behaves like a combination of 'map' and
-- 'foldl'; it applies a function to each element of a ByteString,
-- passing an accumulating parameter from left to right, and returning a
-- final value of this accumulator together with the new ByteString.
{-@ mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> b:LByteString -> (acc, LByteStringSZ b) @-}
mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumL f s0 cs0 = go s0 cs0
  where
    go s Empty        = (s, Empty)
    go s (Chunk c cs) = (s'', Chunk c' cs')
        where (s',  c')  = S.mapAccumL f s c
              (s'', cs') = go s' cs

-- | The 'mapAccumR' function behaves like a combination of 'map' and
-- 'foldr'; it applies a function to each element of a ByteString,
-- passing an accumulating parameter from right to left, and returning a
-- final value of this accumulator together with the new ByteString.
{-@ mapAccumR :: (acc -> Word8 -> (acc, Word8)) -> acc -> b:LByteString -> (acc, LByteStringSZ b) @-}
mapAccumR :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumR f s0 cs0 = go s0 cs0
  where
    go s Empty        = (s, Empty)
    go s (Chunk c cs) = (s'', Chunk c' cs')
        where (s'', c') = S.mapAccumR f s' c
              (s', cs') = go s cs

-- | /O(n)/ map Word8 functions, provided with the index at each position
{-@ mapIndexed :: (Int -> Word8 -> Word8) -> LByteString -> LByteString @-}
mapIndexed :: (Int -> Word8 -> Word8) -> ByteString -> ByteString
mapIndexed f = F.loopArr . F.loopL (F.mapIndexEFL f) 0

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
{-@ scanl :: (Word8 -> Word8 -> Word8) -> Word8 -> b:LByteString
          -> {v:LByteString | (lbLength v) = 1 + (lbLength b)}
  @-}
scanl :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
scanl f z ps = F.loopArr . F.loopL (F.scanEFL f) z $ (ps `snoc` 0)
{-# INLINE scanl #-}

-- ---------------------------------------------------------------------
-- Unfolds and replicates

--LIQUID -- | @'iterate' f x@ returns an infinite ByteString of repeated applications
--LIQUID -- of @f@ to @x@:
--LIQUID --
--LIQUID -- > iterate f x == [x, f x, f (f x), ...]
--LIQUID --
--LIQUID iterate :: (Word8 -> Word8) -> Word8 -> ByteString
--LIQUID iterate f = unfoldr (\x -> case f x of x' -> x' `seq` Just (x', x'))
--LIQUID 
--LIQUID -- | @'repeat' x@ is an infinite ByteString, with @x@ the value of every
--LIQUID -- element.
--LIQUID --
--LIQUID repeat :: Word8 -> ByteString
--LIQUID repeat w = cs where cs = Chunk (S.replicate smallChunkSize w) cs
--LIQUID 
--LIQUID -- | /O(n)/ @'replicate' n x@ is a ByteString of length @n@ with @x@
--LIQUID -- the value of every element.
--LIQUID --
--LIQUID replicate :: Int64 -> Word8 -> ByteString
--LIQUID replicate n w
--LIQUID     | n <= 0             = Empty
--LIQUID     | n < fromIntegral smallChunkSize = Chunk (S.replicate (fromIntegral n) w) Empty
--LIQUID     | r == 0             = cs -- preserve invariant
--LIQUID     | otherwise          = Chunk (S.unsafeTake (fromIntegral r) c) cs
--LIQUID  where
--LIQUID     c      = S.replicate smallChunkSize w
--LIQUID     cs     = nChunks q
--LIQUID     (q, r) = quotRem n (fromIntegral smallChunkSize)
--LIQUID     nChunks 0 = Empty
--LIQUID     nChunks m = Chunk c (nChunks (m-1))
--LIQUID 
--LIQUID -- | 'cycle' ties a finite ByteString into a circular one, or equivalently,
--LIQUID -- the infinite repetition of the original ByteString.
--LIQUID --
--LIQUID cycle :: ByteString -> ByteString
--LIQUID cycle Empty = errorEmptyList "cycle"
--LIQUID cycle cs    = cs' where cs' = foldrChunks Chunk cs' cs
--LIQUID 
--LIQUID -- | /O(n)/ The 'unfoldr' function is analogous to the List \'unfoldr\'.
--LIQUID -- 'unfoldr' builds a ByteString from a seed value.  The function takes
--LIQUID -- the element and returns 'Nothing' if it is done producing the
--LIQUID -- ByteString or returns 'Just' @(a,b)@, in which case, @a@ is a
--LIQUID -- prepending to the ByteString and @b@ is used as the next element in a
--LIQUID -- recursive call.
--LIQUID unfoldr :: (a -> Maybe (Word8, a)) -> a -> ByteString
--LIQUID unfoldr f s0 = unfoldChunk 32 s0
--LIQUID   where unfoldChunk n s =
--LIQUID           case S.unfoldrN n f s of
--LIQUID             (c, Nothing)
--LIQUID               | S.null c  -> Empty
--LIQUID               | otherwise -> Chunk c Empty
--LIQUID             (c, Just s')  -> Chunk c (unfoldChunk (n*2) s')

-- ---------------------------------------------------------------------
-- Substrings

-- | /O(n\/c)/ 'take' @n@, applied to a ByteString @xs@, returns the prefix
-- of @xs@ of length @n@, or @xs@ itself if @n > 'length' xs@.
{-@ take :: n:Nat64
         -> b:LByteString
         -> {v:LByteString | (Min (lbLength v) (lbLength b) n)}
 @-}
take :: Int64 -> ByteString -> ByteString
take i _ | i <= 0 = Empty
take i cs0         = take' i cs0
  where --LIQUID FIXME: (Num a) isn't embedded as int so this loses some
        --LIQUID        refinements without the explicit type
        take' :: Int64 -> ByteString -> ByteString
        take' 0 _            = Empty
        take' _ Empty        = Empty
        take' n (Chunk c cs) =
          if n < fromIntegral (S.length c)
            then Chunk (S.take (fromIntegral n) c) Empty
            else Chunk c (take' (n - fromIntegral (S.length c)) cs)

-- | /O(n\/c)/ 'drop' @n xs@ returns the suffix of @xs@ after the first @n@
-- elements, or @[]@ if @n > 'length' xs@.
{-@ drop :: n:Nat64
         -> b:LByteString
         -> {v:LByteString | ((lbLength v) = (((lbLength b) <= n)
                                           ? 0 : ((lbLength b) - n)))}
  @-}
drop  :: Int64 -> ByteString -> ByteString
drop i p | i <= 0 = p
drop i cs0 = drop' i cs0
  where drop' :: Int64 -> ByteString -> ByteString
        drop' 0 cs           = cs
        drop' _ Empty        = Empty
        drop' n (Chunk c cs) =
          if n < fromIntegral (S.length c)
            then Chunk (S.drop (fromIntegral n) c) cs
            else drop' (n - fromIntegral (S.length c)) cs

-- | /O(n\/c)/ 'splitAt' @n xs@ is equivalent to @('take' n xs, 'drop' n xs)@.
{-@ splitAt :: n:Nat64
            -> b:LByteString
            -> ( {v:LByteString | (Min (lbLength v) (lbLength b) n)}
               , LByteString)<{\x y -> ((lbLength y) = ((lbLength b) - (lbLength x)))}>
  @-}
splitAt :: Int64 -> ByteString -> (ByteString, ByteString)
splitAt i cs0 | i <= 0 = (Empty, cs0)
splitAt i cs0 = splitAt' i cs0
  where splitAt' :: Int64 -> ByteString -> (ByteString, ByteString)
        splitAt' 0 cs           = (Empty, cs)
        splitAt' _ Empty        = (Empty, Empty)
        splitAt' n (Chunk c cs) =
          if n < fromIntegral (S.length c)
            then (Chunk (S.take (fromIntegral n) c) Empty 
                 ,Chunk (S.drop (fromIntegral n) c) cs)
            else let (cs', cs'') = splitAt' (n - fromIntegral (S.length c)) cs
                   in (Chunk c cs', cs'')


-- | 'takeWhile', applied to a predicate @p@ and a ByteString @xs@,
-- returns the longest prefix (possibly empty) of @xs@ of elements that
-- satisfy @p@.
takeWhile :: (Word8 -> Bool) -> ByteString -> ByteString
takeWhile f cs0 = takeWhile' cs0
  where takeWhile' Empty        = Empty
        takeWhile' (Chunk c cs) =
          case findIndexOrEnd (not . f) c of
            0                  -> Empty
            n | n < S.length c -> Chunk (S.take n c) Empty
              | otherwise      -> Chunk c (takeWhile' cs)

-- | 'dropWhile' @p xs@ returns the suffix remaining after 'takeWhile' @p xs@.
dropWhile :: (Word8 -> Bool) -> ByteString -> ByteString
dropWhile f cs0 = dropWhile' cs0
  where dropWhile' Empty        = Empty
        dropWhile' (Chunk c cs) =
          case findIndexOrEnd (not . f) c of
            n | n < S.length c -> Chunk (S.drop n c) cs
              | otherwise      -> dropWhile' cs

-- | 'break' @p@ is equivalent to @'span' ('not' . p)@.
break :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
break f cs0 = break' cs0
  where break' Empty        = (Empty, Empty)
        break' (Chunk c cs) =
          case findIndexOrEnd f c of
            0                  -> (Empty, Chunk c cs)
            n | n < S.length c -> (Chunk (S.take n c) Empty
                                  ,Chunk (S.drop n c) cs)
              | otherwise      -> let (cs', cs'') = break' cs
                                   in (Chunk c cs', cs'')

--
-- TODO
--
-- Add rules
--

{-
-- | 'breakByte' breaks its ByteString argument at the first occurence
-- of the specified byte. It is more efficient than 'break' as it is
-- implemented with @memchr(3)@. I.e.
-- 
-- > break (=='c') "abcd" == breakByte 'c' "abcd"
--
breakByte :: Word8 -> ByteString -> (ByteString, ByteString)
breakByte c (LPS ps) = case (breakByte' ps) of (a,b) -> (LPS a, LPS b)
  where breakByte' []     = ([], [])
        breakByte' (x:xs) =
          case P.elemIndex c x of
            Just 0  -> ([], x : xs)
            Just n  -> (P.take n x : [], P.drop n x : xs)
            Nothing -> let (xs', xs'') = breakByte' xs
                        in (x : xs', xs'')

-- | 'spanByte' breaks its ByteString argument at the first
-- occurence of a byte other than its argument. It is more efficient
-- than 'span (==)'
--
-- > span  (=='c') "abcd" == spanByte 'c' "abcd"
--
spanByte :: Word8 -> ByteString -> (ByteString, ByteString)
spanByte c (LPS ps) = case (spanByte' ps) of (a,b) -> (LPS a, LPS b)
  where spanByte' []     = ([], [])
        spanByte' (x:xs) =
          case P.spanByte c x of
            (x', x'') | P.null x'  -> ([], x : xs)
                      | P.null x'' -> let (xs', xs'') = spanByte' xs
                                       in (x : xs', xs'')
                      | otherwise  -> (x' : [], x'' : xs)
-}

-- | 'span' @p xs@ breaks the ByteString into two segments. It is
-- equivalent to @('takeWhile' p xs, 'dropWhile' p xs)@
span :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
span p = break (not . p)

-- | /O(n)/ Splits a 'ByteString' into components delimited by
-- separators, where the predicate returns True for a separator element.
-- The resulting components do not contain the separators.  Two adjacent
-- separators result in an empty component in the output.  eg.
--
-- > splitWith (=='a') "aabbaca" == ["","","bb","c",""]
-- > splitWith (=='a') []        == []
--
--LIQUID splitWith :: (Word8 -> Bool) -> ByteString -> [ByteString]
--LIQUID splitWith _ Empty          = []
--LIQUID splitWith p (Chunk c0 cs0) = comb [] (S.splitWith p c0) cs0
--LIQUID 
--LIQUID   where comb :: [S.ByteString] -> [S.ByteString] -> ByteString -> [ByteString]
--LIQUID         comb acc (s:[]) Empty        = revChunks (s:acc) : []
--LIQUID         comb acc (s:[]) (Chunk c cs) = comb (s:acc) (S.splitWith p c) cs
--LIQUID         comb acc (s:ss) cs           = revChunks (s:acc) : comb [] ss cs
--LIQUID 
--LIQUID {-# INLINE splitWith #-}

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
--LIQUID split :: Word8 -> ByteString -> [ByteString]
--LIQUID split _ Empty     = []
--LIQUID split w (Chunk c0 cs0) = comb [] (S.split w c0) cs0
--LIQUID 
--LIQUID   where comb :: [S.ByteString] -> [S.ByteString] -> ByteString -> [ByteString]
--LIQUID         comb acc (s:[]) Empty        = revChunks (s:acc) : []
--LIQUID         comb acc (s:[]) (Chunk c cs) = comb (s:acc) (S.split w c) cs
--LIQUID         comb acc (s:ss) cs           = revChunks (s:acc) : comb [] ss cs
--LIQUID {-# INLINE split #-}

{-
-- | Like 'splitWith', except that sequences of adjacent separators are
-- treated as a single separator. eg.
-- 
-- > tokens (=='a') "aabbaca" == ["bb","c"]
--
tokens :: (Word8 -> Bool) -> ByteString -> [ByteString]
tokens f = L.filter (not.null) . splitWith f
-}

-- | The 'group' function takes a ByteString and returns a list of
-- ByteStrings such that the concatenation of the result is equal to the
-- argument.  Moreover, each sublist in the result contains only equal
-- elements.  For example,
--
-- > group "Mississippi" = ["M","i","ss","i","ss","i","pp","i"]
--
-- It is a special case of 'groupBy', which allows the programmer to
-- supply their own equality test.
--LIQUID group :: ByteString -> [ByteString]
--LIQUID group Empty          = []
--LIQUID group (Chunk c0 cs0) = group' [] (S.group c0) cs0
--LIQUID   where 
--LIQUID     group' :: [S.ByteString] -> [S.ByteString] -> ByteString -> [ByteString]
--LIQUID     group' acc@(s':_) ss@(s:_) cs
--LIQUID       | S.unsafeHead s'
--LIQUID      /= S.unsafeHead s             = revNonEmptyChunks    acc  : group' [] ss cs
--LIQUID     group' acc (s:[]) Empty        = revNonEmptyChunks (s:acc) : []
--LIQUID     group' acc (s:[]) (Chunk c cs) = group' (s:acc) (S.group c) cs
--LIQUID     group' acc (s:ss) cs           = revNonEmptyChunks (s:acc) : group' [] ss cs

{-
TODO: check if something like this might be faster

group :: ByteString -> [ByteString]
group xs
    | null xs   = []
    | otherwise = ys : group zs
    where
        (ys, zs) = spanByte (unsafeHead xs) xs
-}

-- | The 'groupBy' function is the non-overloaded version of 'group'.
--
--LIQUID groupBy :: (Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]
--LIQUID groupBy _ Empty          = []
--LIQUID groupBy k (Chunk c0 cs0) = groupBy' [] 0 (S.groupBy k c0) cs0
--LIQUID   where
--LIQUID     groupBy' :: [S.ByteString] -> Word8 -> [S.ByteString] -> ByteString -> [ByteString]
--LIQUID     groupBy' acc@(_:_) c ss@(s:_) cs
--LIQUID       | not (c `k` S.unsafeHead s)     = revNonEmptyChunks acc : groupBy' [] 0 ss cs
--LIQUID     groupBy' acc _ (s:[]) Empty        = revNonEmptyChunks (s : acc) : []
--LIQUID     groupBy' acc w (s:[]) (Chunk c cs) = groupBy' (s:acc) w' (S.groupBy k c) cs
--LIQUID                                            where w' | L.null acc = S.unsafeHead s
--LIQUID                                                     | otherwise  = w
--LIQUID     groupBy' acc _ (s:ss) cs           = revNonEmptyChunks (s : acc) : groupBy' [] 0 ss cs

{-
TODO: check if something like this might be faster

groupBy :: (Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]
groupBy k xs
    | null xs   = []
    | otherwise = take n xs : groupBy k (drop n xs)
    where
        n = 1 + findIndexOrEnd (not . k (head xs)) (tail xs)
-}

-- | /O(n)/ The 'intercalate' function takes a 'ByteString' and a list of
-- 'ByteString's and concatenates the list after interspersing the first
-- argument between each element of the list.
intercalate :: ByteString -> [ByteString] -> ByteString
intercalate s = concat . (L.intersperse s)

join :: ByteString -> [ByteString] -> ByteString
join = intercalate
{-# DEPRECATED join "use intercalate" #-}

-- ---------------------------------------------------------------------
-- Indexing ByteStrings

-- | /O(c)/ 'ByteString' index (subscript) operator, starting from 0.
{-@ index :: b:LByteString -> n:{v:Nat64 | (LBValid b v)} -> Word8 @-}
index :: ByteString -> Int64 -> Word8
index _  i | i < 0  = moduleError "index" ("negative index: " ++ show i)
index cs0 i         = index' cs0 i
  where index' Empty     n = moduleError "index" ("index too large: " ++ show n)
        index' (Chunk c cs) n
          | n >= fromIntegral (S.length c) = 
              index' cs (n - fromIntegral (S.length c))
          | otherwise       = S.unsafeIndex c (fromIntegral n)

--LIQUID -- | /O(n)/ The 'elemIndex' function returns the index of the first
--LIQUID -- element in the given 'ByteString' which is equal to the query
--LIQUID -- element, or 'Nothing' if there is no such element. 
--LIQUID -- This implementation uses memchr(3).
--LIQUID elemIndex :: Word8 -> ByteString -> Maybe Int64
--LIQUID elemIndex w cs0 = elemIndex' 0 cs0
--LIQUID   where elemIndex' _ Empty        = Nothing
--LIQUID         elemIndex' n (Chunk c cs) =
--LIQUID           case S.elemIndex w c of
--LIQUID             Nothing -> elemIndex' (n + fromIntegral (S.length c)) cs
--LIQUID             Just i  -> Just (n + fromIntegral i)
--LIQUID 
--LIQUID {-
--LIQUID -- | /O(n)/ The 'elemIndexEnd' function returns the last index of the
--LIQUID -- element in the given 'ByteString' which is equal to the query
--LIQUID -- element, or 'Nothing' if there is no such element. The following
--LIQUID -- holds:
--LIQUID --
--LIQUID -- > elemIndexEnd c xs == 
--LIQUID -- > (-) (length xs - 1) `fmap` elemIndex c (reverse xs)
--LIQUID --
--LIQUID elemIndexEnd :: Word8 -> ByteString -> Maybe Int
--LIQUID elemIndexEnd ch (PS x s l) = inlinePerformIO $ withForeignPtr x $ \p ->
--LIQUID     go (p `plusPtr` s) (l-1)
--LIQUID   where
--LIQUID     STRICT2(go)
--LIQUID     go p i | i < 0     = return Nothing
--LIQUID            | otherwise = do ch' <- peekByteOff p i
--LIQUID                             if ch == ch'
--LIQUID                                 then return $ Just i
--LIQUID                                 else go p (i-1)
--LIQUID -}
--LIQUID -- | /O(n)/ The 'elemIndices' function extends 'elemIndex', by returning
--LIQUID -- the indices of all elements equal to the query element, in ascending order.
--LIQUID -- This implementation uses memchr(3).
--LIQUID elemIndices :: Word8 -> ByteString -> [Int64]
--LIQUID elemIndices w cs0 = elemIndices' 0 cs0
--LIQUID   where elemIndices' _ Empty        = []
--LIQUID         elemIndices' n (Chunk c cs) = L.map ((+n).fromIntegral) (S.elemIndices w c)
--LIQUID                              ++ elemIndices' (n + fromIntegral (S.length c)) cs
--LIQUID 
--LIQUID -- | count returns the number of times its argument appears in the ByteString
--LIQUID --
--LIQUID -- > count = length . elemIndices
--LIQUID --
--LIQUID -- But more efficiently than using length on the intermediate list.
--LIQUID count :: Word8 -> ByteString -> Int64
--LIQUID count w cs = foldlChunks (\n c -> n + fromIntegral (S.count w c)) 0 cs
--LIQUID 
--LIQUID -- | The 'findIndex' function takes a predicate and a 'ByteString' and
--LIQUID -- returns the index of the first element in the ByteString
--LIQUID -- satisfying the predicate.
--LIQUID findIndex :: (Word8 -> Bool) -> ByteString -> Maybe Int64
--LIQUID findIndex k cs0 = findIndex' 0 cs0
--LIQUID   where findIndex' _ Empty        = Nothing
--LIQUID         findIndex' n (Chunk c cs) =
--LIQUID           case S.findIndex k c of
--LIQUID             Nothing -> findIndex' (n + fromIntegral (S.length c)) cs
--LIQUID             Just i  -> Just (n + fromIntegral i)
--LIQUID {-# INLINE findIndex #-}
--LIQUID 
--LIQUID -- | /O(n)/ The 'find' function takes a predicate and a ByteString,
--LIQUID -- and returns the first element in matching the predicate, or 'Nothing'
--LIQUID -- if there is no such element.
--LIQUID --
--LIQUID -- > find f p = case findIndex f p of Just n -> Just (p ! n) ; _ -> Nothing
--LIQUID --
--LIQUID find :: (Word8 -> Bool) -> ByteString -> Maybe Word8
--LIQUID find f cs0 = find' cs0
--LIQUID   where find' Empty        = Nothing
--LIQUID         find' (Chunk c cs) = case S.find f c of
--LIQUID             Nothing -> find' cs
--LIQUID             Just w  -> Just w
--LIQUID {-# INLINE find #-}
--LIQUID 
--LIQUID -- | The 'findIndices' function extends 'findIndex', by returning the
--LIQUID -- indices of all elements satisfying the predicate, in ascending order.
--LIQUID findIndices :: (Word8 -> Bool) -> ByteString -> [Int64]
--LIQUID findIndices k cs0 = findIndices' 0 cs0
--LIQUID   where findIndices' _ Empty        = []
--LIQUID         findIndices' n (Chunk c cs) = L.map ((+n).fromIntegral) (S.findIndices k c)
--LIQUID                              ++ findIndices' (n + fromIntegral (S.length c)) cs
--LIQUID 
--LIQUID -- ---------------------------------------------------------------------
--LIQUID -- Searching ByteStrings
--LIQUID 
--LIQUID -- | /O(n)/ 'elem' is the 'ByteString' membership predicate.
--LIQUID elem :: Word8 -> ByteString -> Bool
--LIQUID elem w cs = case elemIndex w cs of Nothing -> False ; _ -> True
--LIQUID 
--LIQUID -- | /O(n)/ 'notElem' is the inverse of 'elem'
--LIQUID notElem :: Word8 -> ByteString -> Bool
--LIQUID notElem w cs = not (elem w cs)
--LIQUID 
--LIQUID -- | /O(n)/ 'filter', applied to a predicate and a ByteString,
--LIQUID -- returns a ByteString containing those characters that satisfy the
--LIQUID -- predicate.
--LIQUID filter :: (Word8 -> Bool) -> ByteString -> ByteString
--LIQUID filter p s = go s
--LIQUID     where
--LIQUID         go Empty        = Empty
--LIQUID         go (Chunk x xs) = chunk (S.filter p x) (go xs)
--LIQUID #if __GLASGOW_HASKELL__
--LIQUID {-# INLINE [1] filter #-}
--LIQUID #endif
--LIQUID 
--LIQUID -- | /O(n)/ and /O(n\/c) space/ A first order equivalent of /filter .
--LIQUID -- (==)/, for the common case of filtering a single byte. It is more
--LIQUID -- efficient to use /filterByte/ in this case.
--LIQUID --
--LIQUID -- > filterByte == filter . (==)
--LIQUID --
--LIQUID -- filterByte is around 10x faster, and uses much less space, than its
--LIQUID -- filter equivalent
--LIQUID filterByte :: Word8 -> ByteString -> ByteString
--LIQUID filterByte w ps = replicate (count w ps) w
--LIQUID {-# INLINE filterByte #-}
--LIQUID 
--LIQUID {-# RULES
--LIQUID   "FPS specialise filter (== x)" forall x.
--LIQUID       filter ((==) x) = filterByte x
--LIQUID   #-}
--LIQUID 
--LIQUID {-# RULES
--LIQUID   "FPS specialise filter (== x)" forall x.
--LIQUID      filter (== x) = filterByte x
--LIQUID   #-}
--LIQUID 
--LIQUID {-
--LIQUID -- | /O(n)/ A first order equivalent of /filter . (\/=)/, for the common
--LIQUID -- case of filtering a single byte out of a list. It is more efficient
--LIQUID -- to use /filterNotByte/ in this case.
--LIQUID --
--LIQUID -- > filterNotByte == filter . (/=)
--LIQUID --
--LIQUID -- filterNotByte is around 2x faster than its filter equivalent.
--LIQUID filterNotByte :: Word8 -> ByteString -> ByteString
--LIQUID filterNotByte w (LPS xs) = LPS (filterMap (P.filterNotByte w) xs)
--LIQUID -}
--LIQUID 
--LIQUID -- | /O(n)/ The 'partition' function takes a predicate a ByteString and returns
--LIQUID -- the pair of ByteStrings with elements which do and do not satisfy the
--LIQUID -- predicate, respectively; i.e.,
--LIQUID --
--LIQUID -- > partition p bs == (filter p xs, filter (not . p) xs)
--LIQUID --
--LIQUID partition :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
--LIQUID partition f p = (filter f p, filter (not . f) p)
--LIQUID --TODO: use a better implementation
--LIQUID 
-- ---------------------------------------------------------------------
-- Searching for substrings

-- | /O(n)/ The 'isPrefixOf' function takes two ByteStrings and returns 'True'
-- iff the first is a prefix of the second.
isPrefixOf :: ByteString -> ByteString -> Bool
isPrefixOf Empty _  = True
isPrefixOf _ Empty  = False
isPrefixOf (Chunk x xs) (Chunk y ys)
    | S.length x == S.length y = x == y  && isPrefixOf xs ys
--LIQUID pushing bindings inward for safety
--LIQUID     | S.length x <  S.length y = x == yh && isPrefixOf xs (Chunk yt ys)
--LIQUID     | otherwise                = xh == y && isPrefixOf (Chunk xt xs) ys
--LIQUID   where (xh,xt) = S.splitAt (S.length y) x
--LIQUID         (yh,yt) = S.splitAt (S.length x) y
    | otherwise = let (xh,xt) = S.splitAt (S.length y) x
                      (yh,yt) = S.splitAt (S.length x) y
                  in if S.length x <  S.length y
                     then x == yh && isPrefixOf xs (Chunk yt ys)
                     else  xh == y && isPrefixOf (Chunk xt xs) ys


-- | /O(n)/ The 'isSuffixOf' function takes two ByteStrings and returns 'True'
-- iff the first is a suffix of the second.
-- 
-- The following holds:
--
-- > isSuffixOf x y == reverse x `isPrefixOf` reverse y
--
isSuffixOf :: ByteString -> ByteString -> Bool
isSuffixOf x y = reverse x `isPrefixOf` reverse y
--TODO: a better implementation

--LIQUID -- ---------------------------------------------------------------------
--LIQUID -- Zipping
--LIQUID 
--LIQUID -- | /O(n)/ 'zip' takes two ByteStrings and returns a list of
--LIQUID -- corresponding pairs of bytes. If one input ByteString is short,
--LIQUID -- excess elements of the longer ByteString are discarded. This is
--LIQUID -- equivalent to a pair of 'unpack' operations.
--LIQUID zip :: ByteString -> ByteString -> [(Word8,Word8)]
--LIQUID zip = zipWith (,)
--LIQUID 
--LIQUID -- | 'zipWith' generalises 'zip' by zipping with the function given as
--LIQUID -- the first argument, instead of a tupling function.  For example,
--LIQUID -- @'zipWith' (+)@ is applied to two ByteStrings to produce the list of
--LIQUID -- corresponding sums.
--LIQUID zipWith :: (Word8 -> Word8 -> a) -> ByteString -> ByteString -> [a]
--LIQUID zipWith _ Empty     _  = []
--LIQUID zipWith _ _      Empty = []
--LIQUID zipWith f (Chunk a as) (Chunk b bs) = go a as b bs
--LIQUID   where
--LIQUID     go x xs y ys = f (S.unsafeHead x) (S.unsafeHead y)
--LIQUID                  : to (S.unsafeTail x) xs (S.unsafeTail y) ys
--LIQUID 
--LIQUID     to x Empty         _ _             | S.null x       = []
--LIQUID     to _ _             y Empty         | S.null y       = []
--LIQUID     to x xs            y ys            | not (S.null x)
--LIQUID                                       && not (S.null y) = go x  xs y  ys
--LIQUID     to x xs            _ (Chunk y' ys) | not (S.null x) = go x  xs y' ys
--LIQUID     to _ (Chunk x' xs) y ys            | not (S.null y) = go x' xs y  ys
--LIQUID     to _ (Chunk x' xs) _ (Chunk y' ys)                  = go x' xs y' ys
--LIQUID 
--LIQUID -- | /O(n)/ 'unzip' transforms a list of pairs of bytes into a pair of
--LIQUID -- ByteStrings. Note that this performs two 'pack' operations.
--LIQUID unzip :: [(Word8,Word8)] -> (ByteString,ByteString)
--LIQUID unzip ls = (pack (L.map fst ls), pack (L.map snd ls))
--LIQUID {-# INLINE unzip #-}
--LIQUID 
--LIQUID -- ---------------------------------------------------------------------
--LIQUID -- Special lists
--LIQUID 
--LIQUID -- | /O(n)/ Return all initial segments of the given 'ByteString', shortest first.
--LIQUID inits :: ByteString -> [ByteString]
--LIQUID inits = (Empty :) . inits'
--LIQUID   where inits' Empty        = []
--LIQUID         inits' (Chunk c cs) = L.map (\c' -> Chunk c' Empty) (L.tail (S.inits c))
--LIQUID                            ++ L.map (Chunk c) (inits' cs)
--LIQUID 
--LIQUID -- | /O(n)/ Return all final segments of the given 'ByteString', longest first.
--LIQUID tails :: ByteString -> [ByteString]
--LIQUID tails Empty         = Empty : []
--LIQUID tails cs@(Chunk c cs')
--LIQUID   | S.length c == 1 = cs : tails cs'
--LIQUID   | otherwise       = cs : tails (Chunk (S.unsafeTail c) cs')
--LIQUID 
--LIQUID -- ---------------------------------------------------------------------
--LIQUID -- Low level constructors
--LIQUID 
--LIQUID -- | /O(n)/ Make a copy of the 'ByteString' with its own storage.
--LIQUID --   This is mainly useful to allow the rest of the data pointed
--LIQUID --   to by the 'ByteString' to be garbage collected, for example
--LIQUID --   if a large string has been read in, and only a small part of it
--LIQUID --   is needed in the rest of the program.
--LIQUID copy :: ByteString -> ByteString
--LIQUID copy cs = foldrChunks (Chunk . S.copy) Empty cs
--LIQUID --TODO, we could coalese small blocks here
--LIQUID --FIXME: probably not strict enough, if we're doing this to avoid retaining
--LIQUID -- the parent blocks then we'd better copy strictly.
--LIQUID 
--LIQUID -- ---------------------------------------------------------------------
--LIQUID 
--LIQUID -- TODO defrag func that concatenates block together that are below a threshold
--LIQUID -- defrag :: ByteString -> ByteString
--LIQUID 
--LIQUID -- ---------------------------------------------------------------------
--LIQUID -- Lazy ByteString IO
--LIQUID 
--LIQUID -- | Read entire handle contents /lazily/ into a 'ByteString'. Chunks
--LIQUID -- are read on demand, in at most @k@-sized chunks. It does not block
--LIQUID -- waiting for a whole @k@-sized chunk, so if less than @k@ bytes are
--LIQUID -- available then they will be returned immediately as a smaller chunk.
--LIQUID hGetContentsN :: Int -> Handle -> IO ByteString
--LIQUID hGetContentsN k h = lazyRead
--LIQUID   where
--LIQUID     lazyRead = unsafeInterleaveIO loop
--LIQUID 
--LIQUID     loop = do
--LIQUID         c <- S.hGetNonBlocking h k
--LIQUID         --TODO: I think this should distinguish EOF from no data available
--LIQUID         -- the underlying POSIX call makes this distincion, returning either
--LIQUID         -- 0 or EAGAIN
--LIQUID         if S.null c
--LIQUID           then do eof <- hIsEOF h
--LIQUID                   if eof then return Empty
--LIQUID                          else hWaitForInput h (-1)
--LIQUID                            >> loop
--LIQUID           else do cs <- lazyRead
--LIQUID                   return (Chunk c cs)
--LIQUID 
--LIQUID -- | Read @n@ bytes into a 'ByteString', directly from the
--LIQUID -- specified 'Handle', in chunks of size @k@.
--LIQUID hGetN :: Int -> Handle -> Int -> IO ByteString
--LIQUID hGetN _ _ 0 = return empty
--LIQUID hGetN k h n = readChunks n
--LIQUID   where
--LIQUID     STRICT1(readChunks)
--LIQUID     readChunks i = do
--LIQUID         c <- S.hGet h (min k i)
--LIQUID         case S.length c of
--LIQUID             0 -> return Empty
--LIQUID             m -> do cs <- readChunks (i - m)
--LIQUID                     return (Chunk c cs)
--LIQUID 
--LIQUID -- | hGetNonBlockingN is similar to 'hGetContentsN', except that it will never block
--LIQUID -- waiting for data to become available, instead it returns only whatever data
--LIQUID -- is available. Chunks are read on demand, in @k@-sized chunks.
--LIQUID hGetNonBlockingN :: Int -> Handle -> Int -> IO ByteString
--LIQUID #if defined(__GLASGOW_HASKELL__)
--LIQUID hGetNonBlockingN _ _ 0 = return empty
--LIQUID hGetNonBlockingN k h n = readChunks n
--LIQUID   where
--LIQUID     STRICT1(readChunks)
--LIQUID     readChunks i = do
--LIQUID         c <- S.hGetNonBlocking h (min k i)
--LIQUID         case S.length c of
--LIQUID             0 -> return Empty
--LIQUID             m -> do cs <- readChunks (i - m)
--LIQUID                     return (Chunk c cs)
--LIQUID #else
--LIQUID hGetNonBlockingN = hGetN
--LIQUID #endif
--LIQUID 
--LIQUID -- | Read entire handle contents /lazily/ into a 'ByteString'. Chunks
--LIQUID -- are read on demand, using the default chunk size.
--LIQUID hGetContents :: Handle -> IO ByteString
--LIQUID hGetContents = hGetContentsN defaultChunkSize
--LIQUID 
--LIQUID -- | Read @n@ bytes into a 'ByteString', directly from the specified 'Handle'.
--LIQUID hGet :: Handle -> Int -> IO ByteString
--LIQUID hGet = hGetN defaultChunkSize
--LIQUID 
--LIQUID -- | hGetNonBlocking is similar to 'hGet', except that it will never block
--LIQUID -- waiting for data to become available, instead it returns only whatever data
--LIQUID -- is available.
--LIQUID #if defined(__GLASGOW_HASKELL__)
--LIQUID hGetNonBlocking :: Handle -> Int -> IO ByteString
--LIQUID hGetNonBlocking = hGetNonBlockingN defaultChunkSize
--LIQUID #else
--LIQUID hGetNonBlocking = hGet
--LIQUID #endif
--LIQUID 
--LIQUID -- | Read an entire file /lazily/ into a 'ByteString'.
--LIQUID readFile :: FilePath -> IO ByteString
--LIQUID readFile f = openBinaryFile f ReadMode >>= hGetContents
--LIQUID 
--LIQUID -- | Write a 'ByteString' to a file.
--LIQUID writeFile :: FilePath -> ByteString -> IO ()
--LIQUID writeFile f txt = bracket (openBinaryFile f WriteMode) hClose
--LIQUID     (\hdl -> hPut hdl txt)
--LIQUID 
--LIQUID -- | Append a 'ByteString' to a file.
--LIQUID appendFile :: FilePath -> ByteString -> IO ()
--LIQUID appendFile f txt = bracket (openBinaryFile f AppendMode) hClose
--LIQUID     (\hdl -> hPut hdl txt)
--LIQUID 
--LIQUID -- | getContents. Equivalent to hGetContents stdin. Will read /lazily/
--LIQUID getContents :: IO ByteString
--LIQUID getContents = hGetContents stdin
--LIQUID 
--LIQUID -- | Outputs a 'ByteString' to the specified 'Handle'.
--LIQUID hPut :: Handle -> ByteString -> IO ()
--LIQUID hPut h cs = foldrChunks (\c rest -> S.hPut h c >> rest) (return ()) cs
--LIQUID 
--LIQUID -- | A synonym for @hPut@, for compatibility
--LIQUID hPutStr :: Handle -> ByteString -> IO ()
--LIQUID hPutStr = hPut
--LIQUID 
--LIQUID -- | Write a ByteString to stdout
--LIQUID putStr :: ByteString -> IO ()
--LIQUID putStr = hPut stdout
--LIQUID 
--LIQUID -- | Write a ByteString to stdout, appending a newline byte
--LIQUID putStrLn :: ByteString -> IO ()
--LIQUID putStrLn ps = hPut stdout ps >> hPut stdout (singleton 0x0a)
--LIQUID 
--LIQUID -- | The interact function takes a function of type @ByteString -> ByteString@
--LIQUID -- as its argument. The entire input from the standard input device is passed
--LIQUID -- to this function as its argument, and the resulting string is output on the
--LIQUID -- standard output device. It's great for writing one line programs!
--LIQUID interact :: (ByteString -> ByteString) -> IO ()
--LIQUID interact transformer = putStr . transformer =<< getContents

-- ---------------------------------------------------------------------
-- Internal utilities

-- Common up near identical calls to `error' to reduce the number
-- constant strings created when compiled:
errorEmptyList :: String -> a
errorEmptyList fun = moduleError fun "empty ByteString"

{-@ moduleError :: String -> String -> a @-}
moduleError :: String -> String -> a
moduleError fun msg = error ("Data.ByteString.Lazy." ++ fun ++ ':':' ':msg)


-- reverse a list of non-empty chunks into a lazy ByteString
{-@ revNonEmptyChunks :: [ByteStringNE] -> LByteString @-}
revNonEmptyChunks :: [S.ByteString] -> ByteString
revNonEmptyChunks cs = L.foldl' (flip Chunk) Empty cs

-- reverse a list of possibly-empty chunks into a lazy ByteString
revChunks :: [S.ByteString] -> ByteString
revChunks cs = L.foldl' (flip chunk) Empty cs

{-@ qualif Blah(v:int, l:int, p:GHC.Ptr.Ptr a): (v + (plen p)) >= l @-}

-- | 'findIndexOrEnd' is a variant of findIndex, that returns the length
-- of the string if no element is found, rather than Nothing.
findIndexOrEnd :: (Word8 -> Bool) -> S.ByteString -> Int
findIndexOrEnd k (S.PS x s l) = S.inlinePerformIO $ withForeignPtr x $ \f -> go (f `plusPtr` s) 0
  where
    STRICT2(go)
    go ptr n | n >= l    = return l
             | otherwise = do w <- peek ptr
                              if k w
                                then return n
                                else go (ptr `plusPtr` 1) (n+1)
{-# INLINE findIndexOrEnd #-}
