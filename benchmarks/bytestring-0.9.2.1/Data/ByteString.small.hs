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

module Data.ByteString where

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

import Data.ByteString.Internal hiding (createAndTrim')
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
import Language.Haskell.Liquid.Prelude hiding (eq) 
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

-- for unfoldrN 
{-@ qualif PtrDiffUnfoldrN(v:int, i:int, p:GHC.Ptr.Ptr a): (i - v) <= (plen p) @-}

{-@ lengths :: bs:[ByteString] -> {v:Nat | v = (bLengths bs)} @-}
lengths :: [ByteString] -> Int
lengths []     = 0
lengths (b:bs) = length b + lengths bs

-- LIQUID HACK: this is to get all the quals from memchr. 
-- Quals needed because IO monad forces liquid-abstraction. 
-- Solution, scrape quals from predicate defs (e.g. SuffixPtr)
{-@ dummyForQuals1_elemIndex :: p:(Ptr a) -> n:Int -> (IO {v:(Ptr b) | (SuffixPtr v n p)})  @-}
dummyForQuals1_elemIndex :: Ptr a -> Int -> IO (Ptr b)
dummyForQuals1_elemIndex = undefined 

{-@ dummyForQuals2_splitWith :: p:(ForeignPtr Word8) -> o:{v:Nat | v <= (fplen p)} -> {v:Nat | (BSValid p o v)} -> ByteString 
  @-}
dummyForQuals2_splitWith :: ForeignPtr Word8 -> Int -> Int -> ByteString
dummyForQuals2_splitWith = undefined

-- -----------------------------------------------------------------------------
--
-- Useful macros, until we have bang patterns
--

#define STRICT1(f) f a | a `seq` False = undefined
#define STRICT2(f) f a b | a `seq` b `seq` False = undefined
#define STRICT3(f) f a b c | a `seq` b `seq` c `seq` False = undefined
#define STRICT4(f) f a b c d | a `seq` b `seq` c `seq` d `seq` False = undefined
#define STRICT5(f) f a b c d e | a `seq` b `seq` c `seq` d `seq` e `seq` False = undefined


-- | /O(1)/ The empty 'ByteString'
{-@ empty :: {v:ByteString | (bLength v) = 0} @-} 
empty :: ByteString
empty = PS nullForeignPtr 0 0

 
-- | /O(1)/ Convert a 'Word8' into a 'ByteString'

{-@ singleton :: Word8 -> {v:ByteString | (bLength v) = 1} @-}
singleton :: Word8 -> ByteString
singleton c = unsafeCreate 1 $ \p -> poke p c
{-# INLINE [1] singleton #-}


{-@ qualif PtrDiffUnfoldrN(v:int, i:int, p:GHC.Ptr.Ptr a): (i - v) <= (plen p) @-}

{-@ unfoldrN :: i:Nat -> (a -> Maybe (Word8, a)) -> a -> ({v:ByteString | (bLength v) <= i}, Maybe a)<{\b m -> (((isJust m) && (i>0)) => ((bLength b) > 0))}> @-}
unfoldrN :: Int -> (a -> Maybe (Word8, a)) -> a -> (ByteString, Maybe a)
unfoldrN i f x0
    | i < 0     = (empty, Just x0)
    | otherwise = unsafePerformIO $ createAndTrim' i $ \p -> go p x0 0
  where STRICT3(go)
        go p x n =
          case f x of
            Nothing      -> return (0 :: Int {- LIQUID -}, n, Nothing)
            Just (w,x')
             | n == i    -> return (0, n, Just x)
             | otherwise -> do poke p w
                               go (p `plusPtr` 1) x' (n+1)
{-# INLINE unfoldrN #-}

{-@ measure tfst :: (a,b,c) -> a
    tfst (a,b,c) = a
  @-}
{-@ measure tsnd :: (a,b,c) -> b
    tsnd (a,b,c) = b
  @-}
{-@ measure ttrd :: (a,b,c) -> c
    ttrd (a,b,c) = c
  @-}

{-@ go :: i:Nat -> (a -> Maybe (Word8, a)) -> p:PtrV Word8 -> a -> n:{v:Nat | ((v <= i) && ((i - v) <= (plen p)))}
       -> IO {v0:(Nat,{v:Nat | v>=n}, Maybe a) | (((isJust (ttrd v0)) && (i>0)) => ((tsnd v0)>0))} @-}
go :: Int -> (a -> Maybe (Word8, a)) -> Ptr Word8 -> a -> Int -> IO (Int, Int, Maybe a)
go i f p x n =
    case f x of
      Nothing      -> return (0 :: Int {- LIQUID -}, n, Nothing)
      Just (w,x')
          | n == i    -> return (0, n, Just x)
          | otherwise -> do poke p w
                            go i f (p `plusPtr` 1) x' (n+1)

{-@ qualif Blah(v:Data.Maybe.Maybe a, l:int, i:int): (((isJust v) && (i>0)) => (l>0)) @-}
{-@ qualif Blah(v:Data.Maybe.Maybe a, b:Data.ByteString.Internal.ByteString, i:int): (((isJust v) && (i>0)) => ((bLength b)>0)) @-}

{-@ createAndTrim' :: forall <p :: Int -> Prop>.
                      l:Nat
                   -> ((PtrN Word8 l) -> IO ((Nat, Nat<p>, a)<{\o v -> (v <= l - o)}, {\o l v -> true}>))
                   -> exists[l0:Int<p>].IO ({v:ByteString | (((bLength v) <= l) && (bLength v) = l0)}, a)
  @-}
createAndTrim' :: Int -> (Ptr Word8 -> IO (Int, Int, a)) -> IO (ByteString, a)
createAndTrim' l f = do
    fp <- mallocByteString l
    withForeignPtr fp $ \p -> do
        (off, l', res) <- f p
        if assert (l' <= l) $ l' >= l
            then return $! (PS fp 0 l, res)
            else do ps <- create l' $ \p' ->
                            memcpy p' (p `plusPtr` off) ({- LIQUID fromIntegral -} intCSize l')
                    return $! (ps, res)

{-@ null :: b:ByteString -> {v:Bool | ((Prop v) <=> ((bLength b) = 0))} @-}
null :: ByteString -> Bool
null (PS _ _ l) = assert (l >= 0) $ l <= 0

{-@ length :: b:ByteString -> {v:Nat | v = (bLength b)} @-}
length :: ByteString -> Int
length (PS _ _ l) = assert (l >= 0) $ l

