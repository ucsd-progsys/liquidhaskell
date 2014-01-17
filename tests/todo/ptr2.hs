{-@ LIQUID "--idirs=../../benchmarks/bytestring-0.9.2.1/" @-}
{-@ LIQUID "--idirs=../../include" @-}
{-@ LIQUID "--no-termination" @-}
{-# OPTIONS_GHC -cpp -fglasgow-exts -fno-warn-orphans #-}

-- look for `n0` and `n1` below. Why does this work with `n1` but not `n0` or `0-1` ?
-- the latter is likely some wierd qualifier issue.


module Data.ByteString (
        ByteString,            -- abstract, instances: Eq, Ord, Show, Read, Data, Typeable, Monoid
        foldr                  -- :: (a -> Word8 -> a) -> a -> ByteString -> a
  , wantReadableHandleLIQUID
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
import Language.Haskell.Liquid.Foreign (intCSize, eqPtr) 
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

{- type ByteStringNE   = {v:ByteString | (bLength v) > 0} @-}
{- type ByteStringSZ B = {v:ByteString | (bLength v) = (bLength B)} @-}
-- -----------------------------------------------------------------------------
--
-- Useful macros, until we have bang patterns
--
-- -----------------------------------------------------------------------------
{-@ foldr :: (Word8 -> a -> a) -> a -> ByteString -> a @-}
foldr :: (Word8 -> a -> a) -> a -> ByteString -> a
foldr k v (PS x s l) = inlinePerformIO $ withForeignPtr x $ \ptr ->
        ugo k v (ptr `plusPtr` (s+l-1)) (ptr `plusPtr` (s-1))

{-@ ugo :: (Word8 -> a -> a) -> a -> p:(PtrV Word8) -> {v:Ptr Word8 | ((pbase v) = (pbase p) &&  (plen v) >= (plen p)) } -> IO a @-}
ugo :: (Word8 -> a -> a) -> a -> Ptr Word8 -> Ptr Word8 -> IO a
ugo k z p q | eqPtr q p   = return z
            | otherwise = do c  <- peek p
                             let n0  = -1               -- BAD  
                             let n1  = 0 - 1            -- OK
                             let p' = p `plusPtr` n1 {- BAD (0 - 1) -}
                             ugo k (c `k` z) p' q -- tail recursive


{- liquid_thm_ptr_cmp' :: p:PtrV a
                        -> q:{v:(PtrV a) | ((plen v) >= (plen p) && v != p && (pbase v) = (pbase p))} 
                        -> {v: (PtrV a)  | ((v = p) && ((plen v) > 0) && ((plen q) > (plen p))) } 
  @-}
liquid_thm_ptr_cmp' :: Ptr a -> Ptr a -> Ptr a
liquid_thm_ptr_cmp' p q = undefined 
