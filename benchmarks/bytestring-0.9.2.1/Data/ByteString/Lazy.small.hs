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

module Data.ByteString.Lazy where

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
import qualified Foreign.C.String
import qualified Foreign.C.Types
import Language.Haskell.Liquid.Prelude
import qualified Data.ByteString.Lazy.Aux as SA

-- -----------------------------------------------------------------------------
--
-- Useful macros, until we have bang patterns
--

#define STRICT1(f) f a | a `seq` False = undefined
#define STRICT2(f) f a b | a `seq` b `seq` False = undefined
#define STRICT3(f) f a b c | a `seq` b `seq` c `seq` False = undefined
#define STRICT4(f) f a b c d | a `seq` b `seq` c `seq` d `seq` False = undefined
#define STRICT5(f) f a b c d e | a `seq` b `seq` c `seq` d `seq` e `seq` False = undefined

{- replicate :: n:Nat64 -> Word8 -> {v:LByteString | (lbLength v) = (if n > 0 then n else 0)} @-}
{- replicate :: n:Nat64 -> Word8 -> {v:LByteString | (lbLength v) = n} @-}
replicate :: Int64 -> Word8 -> ByteString
replicate n w
    | n <= 0             = Empty
    | n < fromIntegral smallChunkSize = Chunk (S.replicate (fromIntegral n) w) Empty
    | otherwise =
        let c      = S.replicate smallChunkSize w
            cs     = nChunks q
            (q, r) = quotRem n (fromIntegral smallChunkSize)
            nChunks (0::Int64) = Empty --LIQUID CAST
            nChunks m          = Chunk c (nChunks (m-1))
        in if r == 0 then cs -- preserve invariant
           else Chunk (S.unsafeTake (fromIntegral r) c) cs
--LIQUID     | r == 0             = cs -- preserve invariant
--LIQUID     | otherwise          = Chunk (S.unsafeTake (fromIntegral r) c) cs
--LIQUID  where
--LIQUID     c      = S.replicate smallChunkSize w
--LIQUID     cs     = nChunks q
--LIQUID     (q, r) = quotRem n (fromIntegral smallChunkSize)
--LIQUID     nChunks 0 = Empty
--LIQUID     nChunks m = Chunk c (nChunks (m-1))

{-@ nChunks :: n:Nat64 -> b:ByteStringNE -> {v:LByteString | ((n=0) || ((lbLength v) >= (bLength b)))} @-}
nChunks :: Int64 -> S.ByteString -> ByteString
nChunks 0 c = Empty
nChunks m c = Chunk c (nChunks (m-1) c)

{-@ empty :: {v:LByteString | (lbLength v) = 0} @-}
empty :: ByteString
empty = Empty

{-@ inits :: LByteString -> [LByteString] @-}
inits :: ByteString -> [ByteString]
inits = (Empty :) . inits'
  where inits' Empty        = []
        inits' (Chunk c cs) = let (c':cs') = SA.inits c in
                              L.map (\c' -> Chunk c' Empty) cs' --LIQUID INLINE (L.tail (S.inits c))
                           ++ L.map (Chunk c) (inits' cs)

{- inits :: LByteString -> [LByteString] @-}
-- inits :: ByteString -> [ByteString]
-- inits b = Empty : inits' b
--   where inits' Empty        = []
--         inits' (Chunk c cs) = L.map (\c' -> Chunk c' Empty) cs' --LIQUID (L.tail (SA.inits c))
--                            ++ L.map (Chunk c) (inits' cs)
--              where (_:cs') = SA.inits c

{-@ unzip :: z:[(Word8,Word8)] -> ({v:LByteString | (lbLength v) = (len z)}, {v:LByteString | (lbLength v) = (len z) }) @-}
unzip :: [(Word8,Word8)] -> (ByteString,ByteString)
unzip ls = (pack (L.map fst ls), pack (L.map snd ls))
{-# INLINE unzip #-}

{-@ unzip' :: z:[(Word8,Word8)] -> {v:LByteString | (lbLength v) = (len z)} @-}
unzip' :: [(Word8,Word8)] -> ByteString
unzip' ls = pack (L.map snd ls)

{- predicate LZipLen V X Y  = (len V) = (if (lbLength X) <= (lbLength Y) then (lbLength X) else (lbLength Y)) @-}
{-@ predicate LZipLen V X = (len V) = (lbLength X) @-}
{-@ zip :: x:LByteString -> y:LByteStringSZ x -> {v:[(Word8, Word8)] | (LZipLen v x) } @-}
zip :: ByteString -> ByteString -> [(Word8,Word8)]
zip = zipWith (,)

-- | 'zipWith' generalises 'zip' by zipping with the function given as
-- the first argument, instead of a tupling function.  For example,
-- @'zipWith' (+)@ is applied to two ByteStrings to produce the list of
-- corresponding sums.
{-@ zipWith :: (Word8 -> Word8 -> a) -> x:LByteString -> y:LByteStringSZ x -> {v:[a] | (LZipLen v x)} @-}
zipWith :: (Word8 -> Word8 -> a) -> ByteString -> ByteString -> [a]
zipWith _ Empty     _  = []
zipWith _ _      Empty = []
zipWith f (Chunk a as) (Chunk b bs) = go a as b bs
  where
    go x xs y ys = f (S.unsafeHead x) (S.unsafeHead y)
                 : to (S.unsafeTail x) xs (S.unsafeTail y) ys

    to x Empty         _ _             | S.null x       = []
    to _ _             y Empty         | S.null y       = []
    to x xs            y ys            | not (S.null x)
                                      && not (S.null y) = go x  xs y  ys
    to x xs            _ (Chunk y' ys) | not (S.null x) = go x  xs y' ys
    to _ (Chunk x' xs) y ys            | not (S.null y) = go x' xs y  ys
    to _ (Chunk x' xs) _ (Chunk y' ys)                  = go x' xs y' ys

{- go :: (Word8 -> Word8 -> a) -> x:ByteStringNE -> xs:LByteString -> y:ByteStringNE -> ys:LByteString
       -> {v:[a] | (len v) = (if (((bLength x) + (lbLength xs)) <= ((bLength y) + (lbLength ys)))
                   then ((bLength x) + (lbLength xs))
                   else ((bLength y) + (lbLength ys)))}
  @-}
{-@ go :: (Word8 -> Word8 -> a) -> x:ByteStringNE -> xs:LByteString -> y:ByteStringNE -> ys:{v:LByteString | ((bLength x) + (lbLength xs)) = ((bLength y) + (lbLength v))}
       -> {v:[a] | (len v) = ((bLength x) + (lbLength xs))}
  @-}
go :: (Word8 -> Word8 -> a) -> S.ByteString -> ByteString -> S.ByteString -> ByteString -> [a]
go f x xs y ys = f (S.unsafeHead x) (S.unsafeHead y)
               : to f (S.unsafeTail x) xs (S.unsafeTail y) ys

{- to :: (Word8 -> Word8 -> a) -> x:ByteString -> xs:LByteString -> y:ByteString -> ys:LByteString
       -> {v:[a] | (len v) = (if (((bLength x) + (lbLength xs)) <= ((bLength y) + (lbLength ys)))
                   then ((bLength x) + (lbLength xs))
                   else ((bLength y) + (lbLength ys)))}
  @-}
{-@ to :: (Word8 -> Word8 -> a) -> x:ByteString -> xs:LByteString -> y:ByteString -> ys:{v:LByteString | ((bLength x) + (lbLength xs)) = ((bLength y) + (lbLength v))}
       -> {v:[a] | (len v) = ((bLength x) + (lbLength xs))}
  @-}
to :: (Word8 -> Word8 -> a) -> S.ByteString -> ByteString -> S.ByteString -> ByteString -> [a]
to f x Empty         _ _             | S.null x       = []
to f _ _             y Empty         | S.null y       = []
to f x xs            y ys            | not (S.null x)
                                      && not (S.null y) = go f x  xs y  ys
to f x xs            _ (Chunk y' ys) | not (S.null x) = go f x  xs y' ys
to f x (Chunk x' xs) y ys            | not (S.null y) = go f x' xs y  ys
to f _ (Chunk x' xs) _ (Chunk y' ys)                  = go f x' xs y' ys
-- to f x Empty         y ys            = if S.null x then [] else go f x Empty y ys
-- to f x xs            y Empty         = if S.null y then [] else go f x xs    y Empty
-- to f x (Chunk x' xs) y (Chunk y' ys) = undefined

{-@ isPrefixOf :: LByteString -> LByteString -> Bool @-}
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
    | otherwise = if S.length x <  S.length y
                  then let (xh,xt) = SA.splitAt (S.length y) x
                           (yh,yt) = SA.splitAt (S.length x) y
                       in x == yh && isPrefixOf xs (Chunk yt ys)
                  else let (xh,xt) = SA.splitAt (S.length y) x
                           (yh,yt) = SA.splitAt (S.length x) y
                       in xh == y && isPrefixOf (Chunk xt xs) ys


{- qualif LBZipWith(v:List a,
                     x:Data.ByteString.Internal.ByteString,
                     xs:Data.ByteString.Lazy.Internal.ByteString,
                     y:Data.ByteString.Internal.ByteString,
                     ys:Data.ByteString.Lazy.Internal.ByteString):
        (len v) = (if (((bLength x) + (lbLength xs)) <= ((bLength y) + (lbLength ys)))
                   then ((bLength x) + (lbLength xs))
                   else ((bLength y) + (lbLength ys)))
  @-}

-- reverse a list of non-empty chunks into a lazy ByteString
{-@ revNonEmptyChunks :: bs:[ByteStringNE] -> {v:LByteString | (lbLength v) = (bLengths bs)} @-}
revNonEmptyChunks :: [S.ByteString] -> ByteString
--LIQUID revNonEmptyChunks cs = L.foldl' (flip Chunk) Empty cs
revNonEmptyChunks cs = go Empty cs
    where go acc []     = acc
          go acc (c:cs) = go (Chunk c acc) cs

-- reverse a list of possibly-empty chunks into a lazy ByteString
{-@ revChunks :: bs:[ByteString] -> {v:LByteString | (lbLength v) = (bLengths bs)} @-}
revChunks :: [S.ByteString] -> ByteString
--LIQUID revChunks cs = L.foldl' (flip chunk) Empty cs
revChunks cs = go Empty cs
    where go acc []     = acc
          go acc (c:cs) = go (chunk c acc) cs

{- invariant {v:[LByteString] | (lbLengths v) >= 0} @-}
{- invariant {v:[ByteString]  | (bLengths  v) >= 0} @-}

-- | /O(n)/ Convert a '[Word8]' into a 'ByteString'. 
{-@ pack :: cs:[Word8] -> {v:LByteString | (lbLength v) = (len cs)} @-}
pack :: [Word8] -> ByteString
--LIQUID INLINE pack ws = L.foldr (Chunk . S.pack) Empty (chunks defaultChunkSize ws)
pack ws = go Empty (chunks defaultChunkSize ws)
  where
    go z []     = z
    go z (c:cs) = Chunk (S.pack c) (go z cs)
    chunks :: Int -> [a] -> [[a]]
    chunks _    [] = []
    chunks size xs = case L.splitAt size xs of
                      (xs', xs'') -> xs' : chunks size xs''

-- | /O(n)/ Converts a 'ByteString' to a '[Word8]'.
{-@ unpack :: b:LByteString -> {v:[Word8] | (len v) = (lbLength b)} @-}
unpack :: ByteString -> [Word8]
--LIQUID INLINE unpack cs = L.concatMap S.unpack (toChunks cs)
unpack cs = L.concat $ mapINLINE $ toChunks cs
    where mapINLINE [] = []
          mapINLINE (c:cs) = S.unpack c : mapINLINE cs
--TODO: we can do better here by integrating the concat with the unpack

-- | /O(c)/ Convert a list of strict 'ByteString' into a lazy 'ByteString'
{-@ fromChunks :: bs:[ByteString] -> {v:LByteString | (lbLength v) = (bLengths bs)} @-}
fromChunks :: [S.ByteString] -> ByteString
--LIQUID INLINE fromChunks cs = L.foldr chunk Empty cs
fromChunks []     = Empty
fromChunks (c:cs) = chunk c (fromChunks cs)


-- | /O(n)/ Convert a lazy 'ByteString' into a list of strict 'ByteString'
{-@ toChunks :: b:LByteString -> {v:[ByteString] | (bLengths v) = (lbLength b)} @-}
toChunks :: ByteString -> [S.ByteString]
--LIQUID toChunks cs = foldrChunks (:) [] cs
toChunks cs = foldrChunks (const (:)) [] cs


{-@ mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> b:LByteString -> (acc, LByteStringSZ b) @-}
mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumL f s0 cs0 = go s0 cs0
  where
    go s Empty        = (s, Empty)
    go s (Chunk c cs) = (s'', Chunk c' cs')
        where (s',  c')  = SA.mapAccumL f s c
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
        where (s'', c') = SA.mapAccumR f s' c
              (s', cs') = go s cs








