{--! run liquid with idirs=../../benchmarks/bytestring-0.9.2.1 idirs=../../include no-termination -}
{-# OPTIONS_GHC -cpp -fglasgow-exts -fno-warn-orphans #-}

-- look for `n0` and `n1` below. Why does this work with `n1` but not `n0` or `0-1` ?
-- the latter is likely some wierd qualifier issue.


module Data.ByteString (
        ByteString,            -- abstract, instances: Eq, Ord, Show, Read, Data, Typeable, Monoid
  ) where

import Language.Haskell.Liquid.Prelude

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
import Language.Haskell.Liquid.Prelude (intCSize) 
import qualified Data.ByteString.Lazy.Internal 
import qualified Data.ByteString.Fusion
import qualified Data.ByteString.Internal
import qualified Data.ByteString.Unsafe
import qualified Foreign.C.Types

-- WHY ON EARTH IS THAT LIQUIDASSERT NEEDED?!!!!

{-@ split :: Word8 -> ByteStringNE -> [ByteString] @-}
split :: Word8 -> ByteString -> [ByteString]
-- split _ (PS _ _ 0) = []
split w (PS xanadu s l) = inlinePerformIO $ withForeignPtr xanadu $ \pz -> do
    let p   = liquidAssert (fpLen xanadu == pLen pz) pz
    let ptr = p `plusPtr` s
        loop n =
            let q = inlinePerformIO $ memchr (ptr `plusPtr` n)
                                           w (fromIntegral (l-n))
            in if isNullPtr q {- LIQUID q == nullPtr -}
                then [PS xanadu (s+n) (l-n)]
                else let i' = q `minusPtr` ptr 
                         i  = liquidAssert (i < l) i'       -- LIQUID MYSTERY: why is assert NEEDED HERE (it is!)
                     in PS xanadu (s+n) (i-n) : loop (i+1)

    return (loop 0)


