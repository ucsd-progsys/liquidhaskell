{-@ LIQUID "--pruneunsorted" @-}

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

        -- ** Infinite ByteStrings
        repeat,                 -- :: Word8 -> ByteString
        replicate,              -- :: Int64 -> Word8 -> ByteString
        cycle,                  -- :: ByteString -> ByteString
        iterate,                -- :: (Word8 -> Word8) -> Word8 -> ByteString

        -- ** Unfolding ByteStrings
        unfoldr,                -- :: (a -> Maybe (Word8, a)) -> a -> ByteString

        -- * Substrings

        -- ** Breaking strings
        take,                   -- :: Int64 -> ByteString -> ByteString
        drop,                   -- :: Int64 -> ByteString -> ByteString
        splitAt,                -- :: Int64 -> ByteString -> (ByteString, ByteString)
        takeWhile,              -- :: (Word8 -> Bool) -> ByteString -> ByteString
        dropWhile,              -- :: (Word8 -> Bool) -> ByteString -> ByteString
        span,                   -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
        break,                  -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
        group,                  -- :: ByteString -> [ByteString]
        groupBy,                -- :: (Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]
        inits,                  -- :: ByteString -> [ByteString]
        tails,                  -- :: ByteString -> [ByteString]

        -- ** Breaking into many substrings
        split,                  -- :: Word8 -> ByteString -> [ByteString]
        splitWith,              -- :: (Word8 -> Bool) -> ByteString -> [ByteString]

        -- * Predicates
        isPrefixOf,             -- :: ByteString -> ByteString -> Bool
        isSuffixOf,             -- :: ByteString -> ByteString -> Bool
--        isInfixOf,              -- :: ByteString -> ByteString -> Bool

        -- ** Search for arbitrary substrings
--        isSubstringOf,          -- :: ByteString -> ByteString -> Bool
--        findSubstring,          -- :: ByteString -> ByteString -> Maybe Int
--        findSubstrings,         -- :: ByteString -> ByteString -> [Int]

        -- * Searching ByteStrings

        -- ** Searching by equality
        elem,                   -- :: Word8 -> ByteString -> Bool
        notElem,                -- :: Word8 -> ByteString -> Bool

        -- ** Searching with a predicate
        find,                   -- :: (Word8 -> Bool) -> ByteString -> Maybe Word8
        filter,                 -- :: (Word8 -> Bool) -> ByteString -> ByteString
        partition,              -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)

        -- * Indexing ByteStrings
        index,                  -- :: ByteString -> Int64 -> Word8
        elemIndex,              -- :: Word8 -> ByteString -> Maybe Int64
        elemIndices,            -- :: Word8 -> ByteString -> [Int64]
        findIndex,              -- :: (Word8 -> Bool) -> ByteString -> Maybe Int64
        findIndices,            -- :: (Word8 -> Bool) -> ByteString -> [Int64]
        count,                  -- :: Word8 -> ByteString -> Int64

        -- * Zipping and unzipping ByteStrings
        zip,                    -- :: ByteString -> ByteString -> [(Word8,Word8)]
        zipWith,                -- :: (Word8 -> Word8 -> c) -> ByteString -> ByteString -> [c]
        unzip,                  -- :: [(Word8,Word8)] -> (ByteString,ByteString)

        -- * Ordered ByteStrings
--        sort,                   -- :: ByteString -> ByteString

        -- * Low level conversions
        -- ** Copying ByteStrings
        copy,                   -- :: ByteString -> ByteString
--        defrag,                -- :: ByteString -> ByteString

        -- * I\/O with 'ByteString's

        -- ** Standard input and output
        getContents,            -- :: IO ByteString
        putStr,                 -- :: ByteString -> IO ()
        putStrLn,               -- :: ByteString -> IO ()
        interact,               -- :: (ByteString -> ByteString) -> IO ()

        -- ** Files
        readFile,               -- :: FilePath -> IO ByteString
        writeFile,              -- :: FilePath -> ByteString -> IO ()
        appendFile,             -- :: FilePath -> ByteString -> IO ()

        -- ** I\/O with Handles
        hGetContents,           -- :: Handle -> IO ByteString
        hGet,                   -- :: Handle -> Int -> IO ByteString
        hGetNonBlocking,        -- :: Handle -> Int -> IO ByteString
        hPut,                   -- :: Handle -> ByteString -> IO ()
        hPutStr,                -- :: Handle -> ByteString -> IO ()

--      hGetN,                  -- :: Int -> Handle -> Int -> IO ByteString
--      hGetContentsN,          -- :: Int -> Handle -> IO ByteString
--      hGetNonBlockingN,       -- :: Int -> Handle -> IO ByteString

        -- undocumented deprecated things:
        join                    -- :: ByteString -> [ByteString] -> ByteString

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
import qualified Data.List
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
import Data.ByteString.Fusion   (PairS(..), MaybeS(..))
import Data.Int
import Data.Word                (Word, Word8, Word16, Word32, Word64)
import Foreign.ForeignPtr       (ForeignPtr)

{-@ measure sumLens :: [[a]] -> Int
    sumLens ([])   = 0
    sumLens (x:xs) = len x + (sumLens xs)
  @-}
{-@ invariant {v:[[a]] | sumLens v >= 0} @-}
{-@ qualif SumLensEq(v:List (List a), x:List (List a)): (sumLens v) = (sumLens x) @-}
{-@ qualif SumLensEq(v:List (List a), x:List a): (sumLens v) = (len x) @-}
{-@ qualif SumLensLe(v:List (List a), x:List (List a)): (sumLens v) <= (sumLens x) @-}

-- ByteString qualifiers
{-@ qualif LBLensAcc(v:ByteString,
                     bs:List ByteString,
                     b:ByteString):
        lbLength(v) = lbLengths(bs) + lbLength(b)
  @-}

{-@ qualif ByteStringNE(v:S.ByteString): (bLength v) > 0 @-}
{-@ qualif BLengthsAcc(v:List S.ByteString,
                       c:S.ByteString,
                       cs:List S.ByteString):
        (bLengths v) = (bLength c) + (bLengths cs)
  @-}

{-@ qualif BLengthsSum(v:List (List a), bs:List S.ByteString):
       (sumLens v) = (bLengths bs)
  @-}

{-@ qualif BLenLE(v:S.ByteString, n:int): (bLength v) <= n @-}
{-@ qualif BLenEq(v:S.ByteString,
                  b:S.ByteString):
       (bLength v) = (bLength b)
  @-}

{-@ qualif BLenAcc(v:int,
                   b1:S.ByteString,
                   b2:S.ByteString):
       v = (bLength b1) + (bLength b2)
  @-}
{-@ qualif BLenAcc(v:int,
                   b:S.ByteString,
                   n:int):
       v = (bLength b) + n
  @-}

-- lazy ByteString qualifiers
{-@ qualif LByteStringN(v:ByteString, n:int): (lbLength v) = n @-}
{-@ qualif LByteStringNE(v:ByteString): (lbLength v) > 0 @-}
{-@ qualif LByteStringSZ(v:ByteString,
                         b:ByteString):
        (lbLength v) = (lbLength b)
  @-}

{-@ qualif LBLenAcc(v:int,
                    b1:ByteString,
                    b2:ByteString):
       v = (lbLength b1) + (lbLength b2)
  @-}

{-@ qualif LBLenAcc(v:int,
                    b:ByteString,
                    n:int):
       v = (lbLength b) + n
  @-}

{-@ qualif Chunk(v:ByteString,
                 sb:S.ByteString,
                 lb:ByteString):
       (lbLength v) = (bLength sb) + (lbLength lb)
  @-}

--LIQUID for the myriad `comb` inner functions
{-@ qualif LBComb(v:List ByteString,
                  acc:List S.ByteString,
                  ss:List S.ByteString,
                  cs:ByteString):
        ((lbLengths v) + (len v) - 1) = ((bLengths acc) + ((bLengths ss) + (len ss) - 1) + (lbLength cs))
  @-}

{-@ qualif LBGroup(v:List ByteString,
                   acc:List S.ByteString,
                   ss:List S.ByteString,
                   cs:ByteString):
        (lbLengths v) = ((bLengths acc) + (bLengths ss) + (lbLength cs))
  @-}

{-@ qualif LBLenIntersperse(v:ByteString,
                            sb:S.ByteString,
                            lb:ByteString):
        (lbLength v) = ((bLength sb) * 2) + (lbLength lb)
 @-}

{-@ qualif BLenDouble(v:S.ByteString,
                      b:S.ByteString):
        (bLength v) = (bLength b) * 2
 @-}

{-@ qualif LBLenDouble(v:ByteString,
                       b:ByteString):
        (lbLength v) = (lbLength b) * 2
 @-}

{-@ qualif RevChunksAcc(v:ByteString,
                        acc:ByteString,
                        cs:List S.ByteString):
        (lbLength v) = (lbLength acc) + (bLengths cs)
  @-}

{-@ qualif LBSumLens(v:ByteString,
                     z:ByteString,
                     cs:List (List a)):
        (lbLength v) = (lbLength z) + (sumLens cs)
  @-}
{-@ qualif LBCountAcc(v:int,
                     c:S.ByteString,
                     cs:ByteString):
       v <= (bLength c) + (lbLength cs)
  @-}


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

{-@ eq :: ByteString -> ByteString -> Bool @-}
eq :: ByteString -> ByteString -> Bool
eq Empty Empty = True
eq Empty _     = False
eq _     Empty = False
eq (Chunk a as) (Chunk b bs) =
  case compare (S.length a) (S.length b) of
    LT -> a == (S.take (S.length a) b) && eq as (Chunk (S.drop (S.length a) b) bs)
    EQ -> a == b                       && eq as bs
    GT -> (S.take (S.length b) a) == b && eq (Chunk (S.drop (S.length b) a) as) bs

{-@ cmp :: ByteString -> ByteString -> Ordering @-}
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
{-@ empty :: {v:ByteString | (lbLength v) = 0} @-}
empty :: ByteString
empty = Empty
{-# INLINE empty #-}

-- | /O(1)/ Convert a 'Word8' into a 'ByteString'
{-@ singleton :: Word8 -> {v:ByteString | (lbLength v) = 1} @-}
singleton :: Word8 -> ByteString
singleton w = Chunk (S.singleton w) Empty
{-# INLINE singleton #-}

-- | /O(n)/ Convert a '[Word8]' into a 'ByteString'. 
{-@ pack :: cs:[Word8] -> {v:ByteString | (lbLength v) = (len cs)} @-}
pack :: [Word8] -> ByteString
--LIQUID INLINE pack ws = L.foldr (Chunk . S.pack) Empty (chunks defaultChunkSize ws)
pack ws = go Empty (chunks defaultChunkSize ws)
  where
    {-@ Decrease go 2 @-}
    go z []     = z
    go z (c:cs) = Chunk (S.pack c) (go z cs)
    {-@ Decrease chunks 2 @-}
    chunks :: Int -> [a] -> [[a]]
    chunks _    [] = []
    chunks size xs = case L.splitAt size xs of
                      (xs', xs'') -> xs' : chunks size xs''

-- | /O(n)/ Converts a 'ByteString' to a '[Word8]'.
-- TODO: disabled because type of `concat` changed between ghc 7.8 and 7.10
{- unpack :: b:ByteString -> {v:[Word8] | (len v) = (lbLength b)} @-}
unpack :: ByteString -> [Word8]
--LIQUID INLINE unpack cs = L.concatMap S.unpack (toChunks cs)
unpack cs = L.concat $ mapINLINE $ toChunks cs
    where mapINLINE [] = []
          mapINLINE (c:cs) = S.unpack c : mapINLINE cs
--TODO: we can do better here by integrating the concat with the unpack

-- | /O(c)/ Convert a list of strict 'ByteString' into a lazy 'ByteString'
{-@ fromChunks :: bs:[S.ByteString] -> {v:ByteString | (lbLength v) = (bLengths bs)} @-}
fromChunks :: [S.ByteString] -> ByteString
--LIQUID INLINE fromChunks cs = L.foldr chunk Empty cs
fromChunks []     = Empty
fromChunks (c:cs) = chunk c (fromChunks cs)

-- | /O(n)/ Convert a lazy 'ByteString' into a list of strict 'ByteString'
{-@ toChunks :: b:ByteString -> {v:[S.ByteString] | (bLengths v) = (lbLength b)} @-}
toChunks :: ByteString -> [S.ByteString]
--LIQUID GHOST toChunks cs = foldrChunks (:) [] cs
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
{-@ null :: b:ByteString -> {v:Bool | ((Prop v) <=> ((lbLength b) = 0))} @-}
null :: ByteString -> Bool
null Empty = True
null _     = False
{-# INLINE null #-}

-- | /O(n\/c)/ 'length' returns the length of a ByteString as an 'Int64'
{-@ length :: b:ByteString -> {v:Int64 | v = (lbLength b)} @-}
length :: ByteString -> Int64
--LIQUID GHOST length cs = foldlChunks (\n c -> n + fromIntegral (S.length c)) 0 cs
length cs = foldrChunks (\_ c n -> n + fromIntegral (S.length c)) 0 cs
{-# INLINE length #-}

-- | /O(1)/ 'cons' is analogous to '(:)' for lists.
--
{-@ cons :: Word8 -> b:ByteString -> {v:ByteString | (lbLength v) = ((lbLength b) + 1)}
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
{-@ cons' :: Word8 -> b:ByteString -> {v:ByteString | (lbLength v) = ((lbLength b) + 1)} @-}
cons' :: Word8 -> ByteString -> ByteString
cons' w (Chunk c cs) | S.length c < 16 = Chunk (S.cons w c) cs
cons' w cs                             = Chunk (S.singleton w) cs
{-# INLINE cons' #-}

-- | /O(n\/c)/ Append a byte to the end of a 'ByteString'
{-@ snoc :: b:ByteString -> Word8 -> {v:ByteString | (lbLength v) = ((lbLength b) + 1)} @-}
snoc :: ByteString -> Word8 -> ByteString
--LIQUID GHOST snoc cs w = foldrChunks Chunk (singleton w) cs
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
{-@ uncons :: b:ByteString
           -> Maybe (Word8, {v:ByteString | (lbLength v) = (lbLength b) - 1})
  @-}
uncons :: ByteString -> Maybe (Word8, ByteString)
uncons Empty = Nothing
uncons (Chunk c cs)
    = Just (S.unsafeHead c,
            if S.length c == 1 then cs else Chunk (S.unsafeTail c) cs)
{-# INLINE uncons #-}

-- | /O(1)/ Extract the elements after the head of a ByteString, which must be
-- non-empty.
{-@ tail :: b:LByteStringNE -> {v:ByteString | (lbLength v) = ((lbLength b) - 1)} @-}
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
        {-@ Decrease go 2 @-}
  where go c Empty        = S.last c
        go _ (Chunk c cs) = go c cs
-- XXX Don't inline this. Something breaks with 6.8.2 (haven't investigated yet)

{-@ qualif LBLenAcc(v:ByteString,
                    sb:S.ByteString,
                    lb:ByteString):
        (lbLength v) = ((bLength sb) + (lbLength lb) - 1)
  @-}

-- | /O(n\/c)/ Return all the elements of a 'ByteString' except the last one.
{-@ init :: b:LByteStringNE -> {v:ByteString | (lbLength v) = ((lbLength b) - 1)} @-}
init :: ByteString -> ByteString
init Empty          = errorEmptyList "init"
init (Chunk c0 cs0) = go c0 cs0
        {-@ Decrease go 2 @-}
  where go c Empty | S.length c == 1 = Empty
                   | otherwise       = Chunk (S.init c) Empty
        go c (Chunk c' cs)           = Chunk c (go c' cs)

-- | /O(n\/c)/ Append two ByteStrings
{-@ append :: b1:ByteString -> b2:ByteString
           -> {v:ByteString | (lbLength v) = (lbLength b1) + (lbLength b2)}
  @-}
append :: ByteString -> ByteString -> ByteString
--LIQUID GHOST append xs ys = foldrChunks Chunk ys xs
append xs ys = foldrChunks (const Chunk) ys xs
{-# INLINE append #-}

-- ---------------------------------------------------------------------
-- Transformations

-- | /O(n)/ 'map' @f xs@ is the ByteString obtained by applying @f@ to each
-- element of @xs@.
{-@ map :: (Word8 -> Word8) -> b:ByteString -> (LByteStringSZ b) @-}
map :: (Word8 -> Word8) -> ByteString -> ByteString
map f s = map_go s
    where
        --LIQUID RENAME
        map_go Empty        = Empty
        map_go (Chunk x xs) = Chunk y ys
            where
                y  = S.map f x
                ys = map_go xs
{-# INLINE map #-}

-- | /O(n)/ 'reverse' @xs@ returns the elements of @xs@ in reverse order.
{-@ reverse :: b:ByteString -> (LByteStringSZ b) @-}
reverse :: ByteString -> ByteString
reverse cs0 = rev Empty cs0
        {-@ Decrease rev 2 @-}
  where rev a Empty        = a
        rev a (Chunk c cs) = rev (Chunk (S.reverse c) a) cs
{-# INLINE reverse #-}

-- | The 'intersperse' function takes a 'Word8' and a 'ByteString' and
-- \`intersperses\' that byte between the elements of the 'ByteString'.
-- It is analogous to the intersperse function on Lists.
{-@ intersperse :: Word8 -> b:ByteString
                -> {v:ByteString | if (lbLength b > 0) then (lbLength v = (2 * lbLength b) - 1) else (lbLength v = 0) }
  @-}
intersperse :: Word8 -> ByteString -> ByteString
intersperse _ Empty        = Empty
intersperse w (Chunk c cs) = Chunk (S.intersperse w c)
                                   --LIQUID GHOST (foldrChunks (Chunk . intersperse') Empty cs)
                                   (foldrChunks (\_ c cs -> Chunk (intersperse' c) cs) Empty cs)
  where intersperse' :: S.ByteString -> S.ByteString
        intersperse' (S.PS fp o l) =
          S.unsafeCreate {-LIQUID MULTIPLY (2*l)-} (l+l) $ \p' -> withForeignPtr fp $ \p -> do
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
--LIQUID GHOST foldr k z cs = foldrChunks (flip (S.foldr k)) z cs
foldr k z cs = foldrChunks (const $ flip (S.foldr k)) z cs
{-# INLINE foldr #-}

-- | 'foldl1' is a variant of 'foldl' that has no starting value
-- argument, and thus must be applied to non-empty 'ByteStrings'.
-- This function is subject to array fusion.

--LIQUID FIXME: S.unsafeTail breaks the lazy invariant, but since the
--bytestring is immediately consumed by foldl it may actually be safe

{-@ foldl1 :: (Word8 -> Word8 -> Word8) -> LByteStringNE -> Word8 @-}
foldl1 :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldl1 _ Empty        = errorEmptyList "foldl1"
--LIQUID SAFETY foldl1 f (Chunk c cs) = foldl f (S.unsafeHead c) (Chunk (S.unsafeTail c) cs)
foldl1 f (Chunk c cs) = foldl f (S.unsafeHead c)
                                (case S.unsafeTail c of
                                   c' | S.null c' -> cs
                                      | otherwise -> Chunk c cs)

-- | 'foldl1\'' is like 'foldl1', but strict in the accumulator.
{-@ foldl1' :: (Word8 -> Word8 -> Word8) -> LByteStringNE -> Word8 @-}
foldl1' :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldl1' _ Empty        = errorEmptyList "foldl1'"
--LIQUID SAFETY foldl1' f (Chunk c cs) = foldl' f (S.unsafeHead c) (Chunk (S.unsafeTail c) cs)
foldl1' f (Chunk c cs) = foldl' f (S.unsafeHead c)
                                 (case S.unsafeTail c of
                                    c' | S.null c' -> cs
                                       | otherwise -> Chunk c cs)

-- | 'foldr1' is a variant of 'foldr' that has no starting value argument,
-- and thus must be applied to non-empty 'ByteString's
{-@ foldr1 :: (Word8 -> Word8 -> Word8) -> LByteStringNE -> Word8 @-}
foldr1 :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldr1 _ Empty          = errorEmptyList "foldr1"
foldr1 f (Chunk c0 cs0) = go c0 cs0
        {-@ Decrease go 2 @-}
  where go c Empty         = S.foldr1 f c
        go c (Chunk c' cs) = S.foldr  f (go c' cs) c

-- ---------------------------------------------------------------------
-- Special folds

-- | /O(n)/ Concatenate a list of ByteStrings.
{-@ Lazy concat @-}
{-@ concat :: bs:[ByteString] -> {v:ByteString | (lbLength v) = (lbLengths bs)} @-}
concat :: [ByteString] -> ByteString
concat css0 = to css0
  where
    go Empty        css = to css
    go (Chunk c cs) css = Chunk c (go cs css)
    to []               = Empty
    to (cs:css)         = go cs css

-- | Map a function over a 'ByteString' and concatenate the results

{-@ Lazy concatMap @-}
concatMap :: (Word8 -> ByteString) -> ByteString -> ByteString
concatMap _ Empty        = Empty
concatMap f (Chunk c0 cs0) = to c0 cs0 0
  where
    {-@ Decrease go 1 3 @-}
    go :: S.ByteString -> ByteString -> ByteString -> Int -> ByteString
    go c' cs' Empty        _ = to c' cs' 0
    go c' cs' (Chunk c cs) _ = Chunk c (go c' cs' cs 1)

    {-@ Decrease to 2 3 @-}
    to :: S.ByteString -> ByteString -> Int -> ByteString
    to c cs _ | S.null c  = case cs of
          Empty          -> Empty
          (Chunk c' cs') -> to c' cs' 0
              | otherwise = go (S.unsafeTail c) cs (f (S.unsafeHead c)) 1

-- | /O(n)/ Applied to a predicate and a ByteString, 'any' determines if
-- any element of the 'ByteString' satisfies the predicate.
any :: (Word8 -> Bool) -> ByteString -> Bool
--LIQUID GHOST any f cs = foldrChunks (\c rest -> S.any f c || rest) False cs
any f cs = foldrChunks (\_ c rest -> S.any f c || rest) False cs
{-# INLINE any #-}
-- todo fuse

-- | /O(n)/ Applied to a predicate and a 'ByteString', 'all' determines
-- if all elements of the 'ByteString' satisfy the predicate.
all :: (Word8 -> Bool) -> ByteString -> Bool
--LIQUID GHOST all f cs = foldrChunks (\c rest -> S.all f c && rest) True cs
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
{-@ mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> b:ByteString -> (acc, LByteStringSZ b) @-}
mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumL f s0 cs0 = mapAccum_go s0 cs0
  where
    --LIQUID RENAME
    {-@ Decrease mapAccum_go 2 @-}
    mapAccum_go s Empty        = (s, Empty)
    mapAccum_go s (Chunk c cs) = (s'', Chunk c' cs')
        where (s',  c')  = S.mapAccumL f s c
              (s'', cs') = mapAccum_go s' cs

-- | The 'mapAccumR' function behaves like a combination of 'map' and
-- 'foldr'; it applies a function to each element of a ByteString,
-- passing an accumulating parameter from right to left, and returning a
-- final value of this accumulator together with the new ByteString.
{-@ mapAccumR :: (acc -> Word8 -> (acc, Word8)) -> acc -> b:ByteString -> (acc, LByteStringSZ b) @-}
mapAccumR :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumR f s0 cs0 = go s0 cs0
  where
    {-@ Decrease go 2 @-}
    go s Empty        = (s, Empty)
    go s (Chunk c cs) = (s'', Chunk c' cs')
        where (s'', c') = S.mapAccumR f s' c
              (s', cs') = go s cs

-- | /O(n)/ map Word8 functions, provided with the index at each position
{-@ mapIndexed :: (Int -> Word8 -> Word8) -> ByteString -> ByteString @-}
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
{-LIQUID scanl :: (Word8 -> Word8 -> Word8) -> Word8 -> b:ByteString
          -> {v:ByteString | (lbLength v) = 1 + (lbLength b)}
  @-}
scanl :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
scanl f z ps = F.loopArr . F.loopL (F.scanEFL f) z $ (ps `snoc` 0)
{-# INLINE scanl #-}

-- ---------------------------------------------------------------------
-- Unfolds and replicates

-- | @'iterate' f x@ returns an infinite ByteString of repeated applications
-- of @f@ to @x@:
--
-- > iterate f x == [x, f x, f (f x), ...]
--
{-@ iterate :: (Word8 -> Word8) -> Word8 -> ByteString @-}
{-@ Strict Data.ByteString.Lazy.iterate @-}
iterate :: (Word8 -> Word8) -> Word8 -> ByteString
iterate f = unfoldr (\x -> case f x of x' -> x' `seq` Just (x', x'))

-- | @'repeat' x@ is an infinite ByteString, with @x@ the value of every
-- element.
--
{-@ repeat :: Word8 -> ByteString @-}
{-@ Strict Data.ByteString.Lazy.repeat @-}
repeat :: Word8 -> ByteString
repeat w = cs where cs = Chunk (S.replicate smallChunkSize w) cs

-- | /O(n)/ @'replicate' n x@ is a ByteString of length @n@ with @x@
-- the value of every element.
--
--LIQUID FIXME: can we somehow sneak multiplication into `nChunks`?
{- replicate :: n:Nat64 -> Word8 -> {v:ByteString | (lbLength v) = (if n > 0 then n else 0)} @-}
replicate :: Int64 -> Word8 -> ByteString
replicate n w
    | n <= 0             = Empty
    | n < fromIntegral smallChunkSize = Chunk (S.replicate (fromIntegral n) w) Empty
    | otherwise =
        let c      = S.replicate smallChunkSize w
            cs     = nChunks q
            (q, r) = quotRem n (fromIntegral smallChunkSize)
            --LIQUID CAST
            nChunks (0 :: Int64) = Empty
            nChunks m            = Chunk c (nChunks (m-1))
        in if r == 0 then cs -- preserve invariant
           else Chunk (S.unsafeTake (fromIntegral r) c) cs
--LIQUID LAZY     | r == 0             = cs -- preserve invariant
--LIQUID LAZY     | otherwise          = Chunk (S.unsafeTake (fromIntegral r) c) cs
--LIQUID LAZY  where
--LIQUID LAZY     c      = S.replicate smallChunkSize w
--LIQUID LAZY     cs     = nChunks q
--LIQUID LAZY     (q, r) = quotRem n (fromIntegral smallChunkSize)
--LIQUID LAZY     nChunks 0 = Empty
--LIQUID LAZY     nChunks m = Chunk c (nChunks (m-1))

-- | 'cycle' ties a finite ByteString into a circular one, or equivalently,
-- the infinite repetition of the original ByteString.
--
{-@ cycle :: ByteString -> ByteString @-}
{-@ Strict Data.ByteString.Lazy.cycle @-}
cycle :: ByteString -> ByteString
cycle Empty = errorEmptyList "cycle"
--LIQUID GHOST cycle cs    = cs' where cs' = foldrChunks Chunk cs' cs
cycle cs    = cs' where cs' = foldrChunks (const Chunk) cs' cs

-- | /O(n)/ The 'unfoldr' function is analogous to the List \'unfoldr\'.
-- 'unfoldr' builds a ByteString from a seed value.  The function takes
-- the element and returns 'Nothing' if it is done producing the
-- ByteString or returns 'Just' @(a,b)@, in which case, @a@ is a
-- prepending to the ByteString and @b@ is used as the next element in a
-- recursive call.
{-@ Strict Data.ByteString.Lazy.unfoldr @-}
unfoldr :: (a -> Maybe (Word8, a)) -> a -> ByteString
unfoldr f s0 = unfoldChunk 32 s0
  where unfoldChunk n s =
          case S.unfoldrN n f s of
            (c, Nothing)
              | S.null c  -> Empty
              | otherwise -> Chunk c Empty
            (c, Just s')  -> Chunk c (unfoldChunk (n*2) s')

-- ---------------------------------------------------------------------
-- Substrings

-- | /O(n\/c)/ 'take' @n@, applied to a ByteString @xs@, returns the prefix
-- of @xs@ of length @n@, or @xs@ itself if @n > 'length' xs@.
{-@ take :: n:Nat64
         -> b:ByteString
         -> {v:ByteString | (Min (lbLength v) (lbLength b) n)}
 @-}
take :: Int64 -> ByteString -> ByteString
take i _ | i <= 0 = Empty
take i cs0         = take' i cs0
  where --LIQUID CAST FIXME: (Num a) isn't embedded as int so this loses some
        --LIQUID             refinements without the explicit type
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
         -> b:ByteString
         -> {v:ByteString | lbLength v = (if lbLength b <= n then 0 else (lbLength b - n))}
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
            -> b:ByteString
            -> ( {v:ByteString | (Min (lbLength v) (lbLength b) n)}
               , ByteString)<{\x y -> ((lbLength y) = ((lbLength b) - (lbLength x)))}>
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
{-@ takeWhile :: (Word8 -> Bool) -> b:ByteString -> (LByteStringLE b) @-}
takeWhile :: (Word8 -> Bool) -> ByteString -> ByteString
takeWhile f cs0 = takeWhile' cs0
  where takeWhile' Empty        = Empty
        takeWhile' (Chunk c cs) =
          case findIndexOrEnd (not . f) c of
            0                  -> Empty
            n | n < S.length c -> Chunk (S.take n c) Empty
              | otherwise      -> Chunk c (takeWhile' cs)

-- | 'dropWhile' @p xs@ returns the suffix remaining after 'takeWhile' @p xs@.
{-@ dropWhile :: (Word8 -> Bool) -> b:ByteString -> (LByteStringLE b) @-}
dropWhile :: (Word8 -> Bool) -> ByteString -> ByteString
dropWhile f cs0 = dropWhile' cs0
  where dropWhile' Empty        = Empty
        dropWhile' (Chunk c cs) =
          case findIndexOrEnd (not . f) c of
            n | n < S.length c -> Chunk (S.drop n c) cs
              | otherwise      -> dropWhile' cs

-- | 'break' @p@ is equivalent to @'span' ('not' . p)@.
{-@ break :: (Word8 -> Bool) -> b:ByteString -> (LByteStringPair b) @-}
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
{-@ span :: (Word8 -> Bool) -> b:ByteString -> (LByteStringPair b) @-}
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
{-@ splitWith :: (Word8 -> Bool) -> b:LByteStringNE -> (LByteStringSplit b) @-}
splitWith :: (Word8 -> Bool) -> ByteString -> [ByteString]
splitWith _ Empty     = []
--LIQUID PARAM splitWith w (Chunk c0 cs0) = comb [] (S.splitWith w c0) cs0
--LIQUID PARAM   where comb :: [S.ByteString] -> [S.ByteString] -> ByteString -> [ByteString]
--LIQUID PARAM         comb acc (s:[]) Empty        = revChunks (s:acc) : []
--LIQUID PARAM         comb acc (s:[]) (Chunk c cs) = comb (s:acc) (S.splitWith w c) cs
--LIQUID PARAM         comb acc (s:ss) cs           = revChunks (s:acc) : comb [] ss cs
splitWith w (Chunk c0 cs0) = comb [] cs0 (S.splitWith w c0)
        {-@ Decrease comb 2 3 @-}
  where comb :: [S.ByteString] -> ByteString -> [S.ByteString] -> [ByteString]
        comb acc Empty        (s:[]) = revChunks (s:acc) : []
        comb acc (Chunk c cs) (s:[]) = comb (s:acc) cs (S.splitWith w c)
        comb acc cs           (s:ss) = revChunks (s:acc) : comb [] cs ss

{-# INLINE splitWith #-}

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
{-@ split :: Word8 -> b:LByteStringNE -> (LByteStringSplit b) @-}
split :: Word8 -> ByteString -> [ByteString]
split _ Empty     = []
--LIQUID PARAM split w (Chunk c0 cs0) = comb [] (S.split w c0) cs0
--LIQUID PARAM   where comb :: [S.ByteString] -> [S.ByteString] -> ByteString -> [ByteString]
--LIQUID PARAM         comb acc (s:[]) Empty        = revChunks (s:acc) : []
--LIQUID PARAM         comb acc (s:[]) (Chunk c cs) = comb (s:acc) (S.split w c) cs
--LIQUID PARAM         comb acc (s:ss) cs           = revChunks (s:acc) : comb [] ss cs
split w (Chunk c0 cs0) = comb [] cs0 (S.split w c0)
        {-@ Decrease comb 2 3 @-}
  where comb :: [S.ByteString] -> ByteString -> [S.ByteString] -> [ByteString]
        comb acc Empty        (s:[]) = revChunks (s:acc) : []
        comb acc (Chunk c cs) (s:[]) = comb (s:acc) cs (S.split w c)
        comb acc cs           (s:ss) = revChunks (s:acc) : comb [] cs ss
{-# INLINE split #-}

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
{-@ group :: b:ByteString -> {v: [ByteString] | (lbLengths v) = (lbLength b)} @-}
group :: ByteString -> [ByteString]
group Empty          = []
--LIQUID PARAM group (Chunk c0 cs0) = group' [] (S.group c0) cs0
--LIQUID PARAM   where 
--LIQUID PARAM     group' :: [S.ByteString] -> [S.ByteString] -> ByteString -> [ByteString]
--LIQUID PARAM     group' acc@(s':_) ss@(s:_) cs
--LIQUID PARAM       | S.unsafeHead s'
--LIQUID PARAM      /= S.unsafeHead s             = revNonEmptyChunks    acc  : group' [] ss cs
--LIQUID PARAM     group' acc (s:[]) Empty        = revNonEmptyChunks (s:acc) : []
--LIQUID PARAM     group' acc (s:[]) (Chunk c cs) = group' (s:acc) (S.group c) cs
--LIQUID PARAM     group' acc (s:ss) cs           = revNonEmptyChunks (s:acc) : group' [] ss cs
group (Chunk c0 cs0) = group_go cs0 (S.group c0) []
  where
    {-@ Decrease group_go 1 2 3 @-}
    group_go :: ByteString -> [S.ByteString] -> [S.ByteString] -> [ByteString]
    group_go cs ss@(s:_) acc@(s':_)
      | S.unsafeHead s'
     /= S.unsafeHead s               = revNonEmptyChunks    acc  : group_go cs ss []
    group_go Empty        (s:[]) acc = revNonEmptyChunks (s:acc) : []
    group_go (Chunk c cs) (s:[]) acc = group_go cs (S.group c) (s:acc)
    group_go cs           (s:ss) acc = revNonEmptyChunks (s:acc) : group_go cs ss []

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
{-@ groupBy :: (Word8 -> Word8 -> Bool) -> b:ByteString -> {v:[ByteString] | (lbLengths v) = (lbLength b)} @-}
groupBy :: (Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]
groupBy _ Empty          = []
--LIQUID PARAM groupBy k (Chunk c0 cs0) = groupBy' [] 0 (S.groupBy k c0) cs0
--LIQUID PARAM   where
--LIQUID PARAM     groupBy' :: [S.ByteString] -> Word8 -> [S.ByteString] -> ByteString -> [ByteString]
--LIQUID PARAM     groupBy' acc@(_:_) c ss@(s:_) cs
--LIQUID PARAM       | not (c `k` S.unsafeHead s)     = revNonEmptyChunks acc : groupBy' [] 0 ss cs
--LIQUID PARAM     groupBy' acc _ (s:[]) Empty        = revNonEmptyChunks (s : acc) : []
--LIQUID PARAM     groupBy' acc w (s:[]) (Chunk c cs) = groupBy' (s:acc) w' (S.groupBy k c) cs
--LIQUID PARAM                                            where w' | L.null acc = S.unsafeHead s
--LIQUID PARAM                                                     | otherwise  = w
--LIQUID PARAM     groupBy' acc _ (s:ss) cs           = revNonEmptyChunks (s : acc) : groupBy' [] 0 ss cs
groupBy k (Chunk c0 cs0) = groupBy_go cs0 (S.groupBy k c0) []
  where
    {-@ Decrease groupBy_go 1 2 3 @-}
    groupBy_go :: ByteString -> [S.ByteString] -> [S.ByteString] -> [ByteString]
    groupBy_go cs ss@(s:_) acc@(s':_)
      | S.unsafeHead s'
     /= S.unsafeHead s               = revNonEmptyChunks    acc  : groupBy_go cs ss []
    groupBy_go Empty        (s:[]) acc = revNonEmptyChunks (s:acc) : []
    groupBy_go (Chunk c cs) (s:[]) acc = groupBy_go cs (S.groupBy k c) (s:acc)
    groupBy_go cs           (s:ss) acc = revNonEmptyChunks (s:acc) : groupBy_go cs ss []

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
{-@ index :: b:ByteString -> n:{v:Nat64 | (LBValid b v)} -> Word8 @-}
index :: ByteString -> Int64 -> Word8
index _  i | i < 0  = moduleError "index" ("negative index: " ++ show i)
index cs0 i         = index' cs0 i
  where index' Empty     n = moduleError "index" ("index too large: " ++ show n)
        index' (Chunk c cs) n
          | n >= fromIntegral (S.length c) = 
              index' cs (n - fromIntegral (S.length c))
          | otherwise       = S.unsafeIndex c (fromIntegral n)

-- | /O(n)/ The 'elemIndex' function returns the index of the first
-- element in the given 'ByteString' which is equal to the query
-- element, or 'Nothing' if there is no such element. 
-- This implementation uses memchr(3).
{-@ elemIndex :: Word8 -> b:ByteString -> Maybe {v:Nat64 | v < (lbLength b)} @-}
elemIndex :: Word8 -> ByteString -> Maybe Int64
elemIndex w cs0 = elemIndex_go 0 cs0
        --LIQUID RENAME
        {-@ Decrease elemIndex_go 2 @-}
  where elemIndex_go _          Empty        = Nothing
        elemIndex_go (n::Int64) (Chunk c cs) = --LIQUID CAST
          case S.elemIndex w c of
            Nothing -> elemIndex_go (n + fromIntegral (S.length c)) cs
            Just i  -> Just (n + fromIntegral i)

{-
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
-}

-- | /O(n)/ The 'elemIndices' function extends 'elemIndex', by returning
-- the indices of all elements equal to the query element, in ascending order.
-- This implementation uses memchr(3).
{-@ elemIndices :: Word8 -> b:ByteString -> [{v:Nat64 | v < (lbLength b) }] @-}
elemIndices :: Word8 -> ByteString -> [Int64]
elemIndices w cs0 = elemIndices_go 0 cs0
        --LIQUID RENAME
        {-@ Decrease elemIndices_go 2 @-}
  where elemIndices_go _          Empty        = []
        elemIndices_go (n::Int64) (Chunk c cs) = --LIQUID CAST
            L.map ((+n).fromIntegral) (S.elemIndices w c)
            ++ elemIndices_go (n + fromIntegral (S.length c)) cs

-- | count returns the number of times its argument appears in the ByteString
--
-- > count = length . elemIndices
--
-- But more efficiently than using length on the intermediate list.
{-@ count :: Word8 -> b:ByteString -> {v:Nat64 | v <= (lbLength b) } @-}
count :: Word8 -> ByteString -> Int64
--LIQUID GHOST count w cs = foldlChunks (\n c -> n + fromIntegral (S.count w c)) 0 cs
count w cs = foldrChunks (\_ c n -> n + fromIntegral (S.count w c)) 0 cs

-- | The 'findIndex' function takes a predicate and a 'ByteString' and
-- returns the index of the first element in the ByteString
-- satisfying the predicate.
{-@ findIndex :: (Word8 -> Bool) -> b:ByteString -> (Maybe {v:Nat64 | v < (lbLength b)}) @-}
findIndex :: (Word8 -> Bool) -> ByteString -> Maybe Int64
findIndex k cs0 = findIndex_go 0 cs0
        --LIQUID RENAME
        {-@ Decrease findIndex_go 2 @-}
  where findIndex_go _          Empty        = Nothing
        findIndex_go (n::Int64) (Chunk c cs) = --LIQUID CAST
          case S.findIndex k c of
            Nothing -> findIndex_go (n + fromIntegral (S.length c)) cs
            Just i  -> Just (n + fromIntegral i)
{-# INLINE findIndex #-}

-- | /O(n)/ The 'find' function takes a predicate and a ByteString,
-- and returns the first element in matching the predicate, or 'Nothing'
-- if there is no such element.
--
-- > find f p = case findIndex f p of Just n -> Just (p ! n) ; _ -> Nothing
--
find :: (Word8 -> Bool) -> ByteString -> Maybe Word8
find f cs0 = find' cs0
  where find' Empty        = Nothing
        find' (Chunk c cs) = case S.find f c of
            Nothing -> find' cs
            Just w  -> Just w
{-# INLINE find #-}

-- | The 'findIndices' function extends 'findIndex', by returning the
-- indices of all elements satisfying the predicate, in ascending order.
{-@ findIndices :: (Word8 -> Bool) -> b:ByteString -> [{v:Nat64 | v < (lbLength b)}] @-}
findIndices :: (Word8 -> Bool) -> ByteString -> [Int64]
findIndices k cs0 = findIndices_go 0 cs0
        --LIQUID RENAME
        {-@ Decrease findIndices_go 2 @-}
  where findIndices_go _          Empty        = []
        findIndices_go (n::Int64) (Chunk c cs) = --LIQUID CAST
            L.map ((+n).fromIntegral) (S.findIndices k c)
            ++ findIndices_go (n + fromIntegral (S.length c)) cs

-- ---------------------------------------------------------------------
-- Searching ByteStrings

-- | /O(n)/ 'elem' is the 'ByteString' membership predicate.
elem :: Word8 -> ByteString -> Bool
elem w cs = case elemIndex w cs of Nothing -> False ; _ -> True

-- | /O(n)/ 'notElem' is the inverse of 'elem'
notElem :: Word8 -> ByteString -> Bool
notElem w cs = not (elem w cs)

-- | /O(n)/ 'filter', applied to a predicate and a ByteString,
-- returns a ByteString containing those characters that satisfy the
-- predicate.
{-@ filter :: (Word8 -> Bool) -> b:ByteString -> (LByteStringLE b) @-}
filter :: (Word8 -> Bool) -> ByteString -> ByteString
filter p s = filter_go s
    where
        --LIQUID RENAME
        filter_go Empty        = Empty
        filter_go (Chunk x xs) = chunk (S.filter p x) (filter_go xs)
#if __GLASGOW_HASKELL__
{-# INLINE [1] filter #-}
#endif

-- | /O(n)/ and /O(n\/c) space/ A first order equivalent of /filter .
-- (==)/, for the common case of filtering a single byte. It is more
-- efficient to use /filterByte/ in this case.
--
-- > filterByte == filter . (==)
--
-- filterByte is around 10x faster, and uses much less space, than its
-- filter equivalent
--LIQUID TODO: needs the spec for replicate
{- filterByte :: Word8 -> b:ByteString -> (LByteStringLE b) @-}
filterByte :: Word8 -> ByteString -> ByteString
filterByte w ps = replicate (count w ps) w
{-# INLINE filterByte #-}

{-# RULES
  "FPS specialise filter (== x)" forall x.
      filter ((==) x) = filterByte x
  #-}

{-# RULES
  "FPS specialise filter (== x)" forall x.
     filter (== x) = filterByte x
  #-}

{-
-- | /O(n)/ A first order equivalent of /filter . (\/=)/, for the common
-- case of filtering a single byte out of a list. It is more efficient
-- to use /filterNotByte/ in this case.
--
-- > filterNotByte == filter . (/=)
--
-- filterNotByte is around 2x faster than its filter equivalent.
filterNotByte :: Word8 -> ByteString -> ByteString
filterNotByte w (LPS xs) = LPS (filterMap (P.filterNotByte w) xs)
-}

-- | /O(n)/ The 'partition' function takes a predicate a ByteString and returns
-- the pair of ByteStrings with elements which do and do not satisfy the
-- predicate, respectively; i.e.,
--
-- > partition p bs == (filter p xs, filter (not . p) xs)
--
{-@ partition :: (Word8 -> Bool) -> b:ByteString -> ((LByteStringLE b), (LByteStringLE b)) @-}
partition :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
partition f p = (filter f p, filter (not . f) p)
--TODO: use a better implementation

-- ---------------------------------------------------------------------
-- Searching for substrings

-- | /O(n)/ The 'isPrefixOf' function takes two ByteStrings and returns 'True'
-- iff the first is a prefix of the second.
{-@ isPrefixOf :: ByteString -> ByteString -> Bool @-}
isPrefixOf :: ByteString -> ByteString -> Bool
isPrefixOf Empty _  = True
isPrefixOf _ Empty  = False
isPrefixOf (Chunk x xs) (Chunk y ys)
    | S.length x == S.length y = x == y  && isPrefixOf xs ys
--LIQUID LAZY pushing bindings inward for safety
--LIQUID LAZY     | S.length x <  S.length y = x == yh && isPrefixOf xs (Chunk yt ys)
--LIQUID LAZY     | otherwise                = xh == y && isPrefixOf (Chunk xt xs) ys
--LIQUID LAZY   where (xh,xt) = S.splitAt (S.length y) x
--LIQUID LAZY         (yh,yt) = S.splitAt (S.length x) y
    | otherwise = if S.length x <  S.length y
                  then let (xh,xt) = S.splitAt (S.length y) x
                           (yh,yt) = S.splitAt (S.length x) y
                       in x == yh && isPrefixOf xs (Chunk yt ys)
                  else let (xh,xt) = S.splitAt (S.length y) x
                           (yh,yt) = S.splitAt (S.length x) y
                       in xh == y && isPrefixOf (Chunk xt xs) ys


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

-- ---------------------------------------------------------------------
-- Zipping

--LIQUID TODO: zip and zipWith are in LazyZip.hs because they need a
--qualifier that takes 4 parameters and this module is slow enough to
--verify as is.

-- | /O(n)/ 'zip' takes two ByteStrings and returns a list of
-- corresponding pairs of bytes. If one input ByteString is short,
-- excess elements of the longer ByteString are discarded. This is
-- equivalent to a pair of 'unpack' operations.
{-@ predicate LZipLen V X Y  = (len V) = (if (lbLength X) <= (lbLength Y) then (lbLength X) else (lbLength Y)) @-}
{-@ zip :: x:ByteString -> y:ByteString -> {v:[(Word8, Word8)] | (LZipLen v x y) } @-}
zip :: ByteString -> ByteString -> [(Word8,Word8)]
zip = zipWith (,)

-- | 'zipWith' generalises 'zip' by zipping with the function given as
-- the first argument, instead of a tupling function.  For example,
-- @'zipWith' (+)@ is applied to two ByteStrings to produce the list of
-- corresponding sums.
{-@ zipWith :: (Word8 -> Word8 -> a) -> x:ByteString -> y:ByteString -> {v:[a] | (LZipLen v x y)} @-}
--LIQUID see LazyZip.hs
zipWith :: (Word8 -> Word8 -> a) -> ByteString -> ByteString -> [a]
zipWith = undefined
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

-- | /O(n)/ 'unzip' transforms a list of pairs of bytes into a pair of
-- ByteStrings. Note that this performs two 'pack' operations.
{-@ unzip :: z:[(Word8,Word8)] -> ({v:ByteString | (lbLength v) = (len z)}, {v:ByteString | (lbLength v) = (len z) }) @-}
unzip :: [(Word8,Word8)] -> (ByteString,ByteString)
unzip ls = (pack (L.map fst ls), pack (L.map snd ls))
{-# INLINE unzip #-}

-- ---------------------------------------------------------------------
-- Special lists

-- | /O(n)/ Return all initial segments of the given 'ByteString', shortest first.
{-@ inits :: ByteString -> [ByteString] @-}
inits :: ByteString -> [ByteString]
inits = (Empty :) . inits'

  where inits' Empty        = []
        inits' (Chunk c cs) = let (c':cs') = S.inits c in
                              L.map (\c' -> Chunk c' Empty) cs' --LIQUID INLINE (L.tail (S.inits c))
                           ++ L.map (Chunk c) (inits' cs)

-- | /O(n)/ Return all final segments of the given 'ByteString', longest first.
{-@ tails :: ByteString -> [ByteString] @-}
tails :: ByteString -> [ByteString]
tails Empty         = Empty : []
tails cs@(Chunk c cs')
  | S.length c == 1 = cs : tails cs'
  | otherwise       = cs : tails (Chunk (S.unsafeTail c) cs')

-- ---------------------------------------------------------------------
-- Low level constructors

-- | /O(n)/ Make a copy of the 'ByteString' with its own storage.
--   This is mainly useful to allow the rest of the data pointed
--   to by the 'ByteString' to be garbage collected, for example
--   if a large string has been read in, and only a small part of it
--   is needed in the rest of the program.
{-@ copy :: b:ByteString -> LByteStringSZ b @-}
copy :: ByteString -> ByteString
--LIQUID GHOST copy cs = foldrChunks (Chunk . S.copy) Empty cs
copy cs = foldrChunks (\_ c cs -> Chunk (S.copy c) cs) Empty cs
--TODO, we could coalese small blocks here
--FIXME: probably not strict enough, if we're doing this to avoid retaining
-- the parent blocks then we'd better copy strictly.

-- ---------------------------------------------------------------------

-- TODO defrag func that concatenates block together that are below a threshold
-- defrag :: ByteString -> ByteString

-- ---------------------------------------------------------------------
-- Lazy ByteString IO

-- | Read entire handle contents /lazily/ into a 'ByteString'. Chunks
-- are read on demand, in at most @k@-sized chunks. It does not block
-- waiting for a whole @k@-sized chunk, so if less than @k@ bytes are
-- available then they will be returned immediately as a smaller chunk.
{-@ hGetContentsN :: Nat -> Handle -> IO ByteString @-}
hGetContentsN :: Int -> Handle -> IO ByteString
hGetContentsN k h = lazyRead
  where
    {-@ Lazy lazyRead @-}
    lazyRead = unsafeInterleaveIO loop
    {-@ Lazy loop @-}
    loop = do
        c <- S.hGetNonBlocking h k
        --TODO: I think this should distinguish EOF from no data available
        -- the underlying POSIX call makes this distincion, returning either
        -- 0 or EAGAIN
        if S.null c
          then do eof <- hIsEOF h
                  if eof then return Empty
                         else hWaitForInput h (-1)
                           >> loop
          else do cs <- lazyRead
                  return (Chunk c cs)

-- | Read @n@ bytes into a 'ByteString', directly from the
-- specified 'Handle', in chunks of size @k@.
{-@ hGetN :: Nat -> Handle -> n:Nat -> IO {v:ByteString | (lbLength v) <= n} @-}
hGetN :: Int -> Handle -> Int -> IO ByteString
hGetN _ _ 0 = return empty
hGetN k h n = readChunks n
  where
    STRICT1(readChunks)
    readChunks i = do
        c <- S.hGet h (min k i)
        case S.length c of
            0 -> return Empty
            m -> do cs <- readChunks (i - m)
                    return (Chunk c cs)

-- | hGetNonBlockingN is similar to 'hGetContentsN', except that it will never block
-- waiting for data to become available, instead it returns only whatever data
-- is available. Chunks are read on demand, in @k@-sized chunks.
{-@ hGetNonBlockingN :: Nat -> Handle -> n:Nat -> IO {v:ByteString | (lbLength v) <= n} @-}
hGetNonBlockingN :: Int -> Handle -> Int -> IO ByteString
#if defined(__GLASGOW_HASKELL__)
hGetNonBlockingN _ _ 0 = return empty
hGetNonBlockingN k h n = readChunks n
  where
    STRICT1(readChunks)
    readChunks i = do
        c <- S.hGetNonBlocking h (min k i)
        case S.length c of
            0 -> return Empty
            m -> do cs <- readChunks (i - m)
                    return (Chunk c cs)
#else
hGetNonBlockingN = hGetN
#endif

-- | Read entire handle contents /lazily/ into a 'ByteString'. Chunks
-- are read on demand, using the default chunk size.
hGetContents :: Handle -> IO ByteString
hGetContents = hGetContentsN defaultChunkSize

-- | Read @n@ bytes into a 'ByteString', directly from the specified 'Handle'.
{-@ hGet :: Handle -> Nat -> IO ByteString @-}
hGet :: Handle -> Int -> IO ByteString
hGet = hGetN defaultChunkSize

-- | hGetNonBlocking is similar to 'hGet', except that it will never block
-- waiting for data to become available, instead it returns only whatever data
-- is available.
#if defined(__GLASGOW_HASKELL__)
{-@ hGetNonBlocking :: Handle -> Nat -> IO ByteString @-}
hGetNonBlocking :: Handle -> Int -> IO ByteString
hGetNonBlocking = hGetNonBlockingN defaultChunkSize
#else
hGetNonBlocking = hGet
#endif

-- | Read an entire file /lazily/ into a 'ByteString'.
readFile :: FilePath -> IO ByteString
readFile f = openBinaryFile f ReadMode >>= hGetContents

-- | Write a 'ByteString' to a file.
writeFile :: FilePath -> ByteString -> IO ()
writeFile f txt = bracket (openBinaryFile f WriteMode) hClose
    (\hdl -> hPut hdl txt)

-- | Append a 'ByteString' to a file.
appendFile :: FilePath -> ByteString -> IO ()
appendFile f txt = bracket (openBinaryFile f AppendMode) hClose
    (\hdl -> hPut hdl txt)

-- | getContents. Equivalent to hGetContents stdin. Will read /lazily/
getContents :: IO ByteString
getContents = hGetContents stdin

-- | Outputs a 'ByteString' to the specified 'Handle'.
hPut :: Handle -> ByteString -> IO ()
--LIQUID GHOST hPut h cs = foldrChunks (\c rest -> S.hPut h c >> rest) (return ()) cs
hPut h cs = foldrChunks (\_ c rest -> S.hPut h c >> rest) (return ()) cs

-- | A synonym for @hPut@, for compatibility
hPutStr :: Handle -> ByteString -> IO ()
hPutStr = hPut

-- | Write a ByteString to stdout
putStr :: ByteString -> IO ()
putStr = hPut stdout

-- | Write a ByteString to stdout, appending a newline byte
putStrLn :: ByteString -> IO ()
putStrLn ps = hPut stdout ps >> hPut stdout (singleton 0x0a)

-- | The interact function takes a function of type @ByteString -> ByteString@
-- as its argument. The entire input from the standard input device is passed
-- to this function as its argument, and the resulting string is output on the
-- standard output device. It's great for writing one line programs!
interact :: (ByteString -> ByteString) -> IO ()
interact transformer = putStr . transformer =<< getContents

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
{-@ revNonEmptyChunks :: bs:[ByteStringNE] -> {v:ByteString | (lbLength v) = (bLengths bs)} @-}
revNonEmptyChunks :: [S.ByteString] -> ByteString
--LIQUID INLINE revNonEmptyChunks cs = L.foldl' (flip Chunk) Empty cs
revNonEmptyChunks cs = go Empty cs
          {-@ Decrease go 2 @-}
    where go acc []     = acc
          go acc (c:cs) = go (Chunk c acc) cs

-- reverse a list of possibly-empty chunks into a lazy ByteString
{-@ revChunks :: bs:[S.ByteString] -> {v:ByteString | (lbLength v) = (bLengths bs)} @-}
revChunks :: [S.ByteString] -> ByteString
--LIQUID INLINE revChunks cs = L.foldl' (flip chunk) Empty cs
revChunks cs = go Empty cs
          {-@ Decrease go 2 @-}
    where go acc []     = acc
          go acc (c:cs) = go (chunk c acc) cs

{-@ qualif Blah(v:int, l:int, p:Ptr a): (v + (plen p)) >= l @-}

-- | 'findIndexOrEnd' is a variant of findIndex, that returns the length
-- of the string if no element is found, rather than Nothing.
findIndexOrEnd :: (Word8 -> Bool) -> S.ByteString -> Int
findIndexOrEnd k (S.PS x s l) = S.inlinePerformIO $ withForeignPtr x $ \f -> go l (f `plusPtr` s) 0
  where
    --LIQUID GHOST
    STRICT3(go)
    {- LIQUID WITNESS -}
    go (d::Int) ptr n
        | n >= l    = return l
        | otherwise = do w <- peek ptr
                         if k w
                         then return n
                         else go (d-1) (ptr `plusPtr` 1) (n+1)
{-# INLINE findIndexOrEnd #-}

{- liquidCanary :: x:Int -> {v: Int | v > x} @-}
liquidCanary     :: Int -> Int
liquidCanary x   = x - 1
