{--! run liquid with idirs=../../benchmarks/bytestring-0.9.2.1 idirs=../../include no-termination -}
{-# OPTIONS_GHC -cpp -fglasgow-exts -fno-warn-orphans #-}

-- GET THIS TO WORK WITHOUT THE "base" measure and realated theorem,
-- but with raw pointer arithmetic. I.e. give plusPtr the right signature:
--   (v = base + off)
-- Can do so now, by:
--
--   embed Ptr as int 
--
-- but the problem is that then it throws off all qualifier definitions like
--  
--   qualif EqPLen(v: ForeignPtr a, x: Ptr a): (fplen v) = (plen x)
--   qualif EqPLen(v: Ptr a, x: ForeignPtr a): (plen v) = (fplen x) 
-- 
-- because there is no such thing as Ptr a by the time we get to Fixpoint. yuck.
-- Meaning we have to rewrite the above to the rather lame:

--   qualif EqPLenPOLY2(v: a, x: b): (plen v) = (fplen x)           


module Data.ByteString (
        ByteString,            -- abstract, instances: Eq, Ord, Show, Read, Data, Typeable, Monoid
        foldl                  -- :: (a -> Word8 -> a) -> a -> ByteString -> a
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

#define STRICT1(f) f a | a `seq` False = undefined
#define STRICT2(f) f a b | a `seq` b `seq` False = undefined
#define STRICT3(f) f a b c | a `seq` b `seq` c `seq` False = undefined
#define STRICT4(f) f a b c d | a `seq` b `seq` c `seq` d `seq` False = undefined
#define STRICT5(f) f a b c d e | a `seq` b `seq` c `seq` d `seq` e `seq` False = undefined

-- -----------------------------------------------------------------------------

{-@ foldl :: (a -> Word8 -> a) -> a -> ByteString -> a @-}
foldl :: (a -> Word8 -> a) -> a -> ByteString -> a
foldl f v (PS x s l) = inlinePerformIO $ withForeignPtr x $ \ptr ->
        lgo v (ptr `plusPtr` s) (ptr `plusPtr` (s+l))
    where
        STRICT3(lgo)
        lgo z p q | eqPtr p q    = return z
                  | otherwise = do c <- peek p
                                   lgo (f z c) (p `plusPtr` 1) q
{-# INLINE foldl #-}

{- liquid_thm_ptr_cmp :: p:PtrV a
                       -> q:{v:(PtrV a) | ((plen v) <= (plen p) && v != p && (pbase v) = (pbase p))} 
                       -> {v: (PtrV a)  | ((v = p) && ((plen q) < (plen p))) } 
  @-}
liquid_thm_ptr_cmp :: Ptr a -> Ptr a -> Ptr a
liquid_thm_ptr_cmp p q = p 

-- | 'foldl\'' is like 'foldl', but strict in the accumulator.
-- Though actually foldl is also strict in the accumulator.
foldl' :: (a -> Word8 -> a) -> a -> ByteString -> a
foldl' = foldl
{-# INLINE foldl' #-}


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


