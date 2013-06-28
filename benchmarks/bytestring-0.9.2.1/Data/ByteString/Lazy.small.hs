{-# OPTIONS_GHC -cpp -fglasgow-exts -fno-warn-orphans #-}

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
    ,getContents,getLine,putStr,putStrLn ,zip,zipWith,unzip,notElem
    --LIQUID
    ,quotRem)

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

{-@ measure mul :: Int64 -> Int64 -> Int64  @-}
{-@ invariant {v:ByteString | (mul (bLength v) 0) = 0} @-}
{-@ axiom_mul :: b:LByteString -> c:ByteString -> cs:LByteString -> n:Nat64
              -> {v:Bool | ((Prop v) <=> ((((lbLength cs) = (mul (bLength c) (n-1)))
                                           && ((lbLength b) = ((bLength c) + (lbLength cs))))
                                          => ((lbLength b)  = (mul (bLength c) n))))}
  @-}
axiom_mul :: ByteString -> S.ByteString -> ByteString -> Int64 -> Bool
axiom_mul = undefined

{-@ qualif LBLenMul(v:Data.ByteString.Lazy.Internal.ByteString,
                    b:Data.ByteString.Internal.ByteString, n:int):
        (lbLength v) = (mul (bLength b) (n-1))
  @-}

{-@ quotRem :: x:Int64 -> y:Int64 -> ({v:Int64 | ((v = (x / y)) && (((x>=0) && (y>=0)) => (v>=0)) && (((x>=0) && (y>=1)) => (v<=x)))}
                                                                 ,{v:Int64 | ((v >= 0) && (v < y))})<{\q r -> x = (r + (mul y q))}>
  @-}
quotRem :: Int64 -> Int64 -> (Int64,Int64)
quotRem = undefined

{- replicate :: n:Nat64 -> Word8 -> {v:LByteString | (lbLength v) = (if n > 0 then n else 0)} @-}
{-@ replicate :: n:Nat64 -> Word8 -> {v:LByteString | (lbLength v) = n} @-}
replicate :: Int64 -> Word8 -> ByteString
replicate n w
    | n <= 0             = Empty
    | n < fromIntegral smallChunkSize = Chunk (S.replicate (fromIntegral n) w) Empty
    | otherwise =
        let c      = S.replicate smallChunkSize w
            cs     = nChunks q c
            (q, r) = quotRem n (fromIntegral smallChunkSize)
            -- nChunks (0::Int64) = Empty --LIQUID CAST
            -- nChunks m          = Chunk c (nChunks (m-1))
        in if r == 0 then cs -- preserve invariant
           else undefined --Chunk (S.unsafeTake (fromIntegral r) c) cs
--LIQUID     | r == 0             = cs -- preserve invariant
--LIQUID     | otherwise          = Chunk (S.unsafeTake (fromIntegral r) c) cs
--LIQUID  where
--LIQUID     c      = S.replicate smallChunkSize w
--LIQUID     cs     = nChunks q
--LIQUID     (q, r) = quotRem n (fromIntegral smallChunkSize)
--LIQUID     nChunks 0 = Empty
--LIQUID     nChunks m = Chunk c (nChunks (m-1))

{-@ nChunks :: n:Nat64 -> b:ByteStringNE -> {v:LByteString | (lbLength v) = (mul (bLength b) n)} @-}
nChunks :: Int64 -> S.ByteString -> ByteString
nChunks 0 c = Empty
nChunks m c = let cs = (nChunks (m-1) c)
                  b = Chunk c cs
              in liquidAssume (axiom_mul b c cs m) cs

{-@ empty :: {v:LByteString | (lbLength v) = 0} @-}
empty :: ByteString
empty = Empty









