{-# OPTIONS_GHC -cpp -fglasgow-exts -fno-warn-orphans #-}

module Data.ByteStringHelper  where

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
import Language.Haskell.Liquid.Prelude -- (isNullPtr, liquidAssert, intCSize) 
import qualified Data.ByteString.Lazy.Internal 
import qualified Data.ByteString.Fusion
import qualified Data.ByteString.Internal
import qualified Data.ByteString.Unsafe
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


{-@ include <ByteString.hs.hquals> @-}

-- -----------------------------------------------------------------------------
-- LIQUID: This will go away when we properly embed Ptr a as int -- only in
-- fixpoint to avoid the Sort mismatch hassles. 
{-@ liquid_thm_ptr_cmp :: p:PtrV a 
                       -> q:{v:(PtrV a) | ((plen v) <= (plen p) && v != p && (pbase v) = (pbase p))} 
                       -> {v: (PtrV a)  | ((v = p) && ((plen q) < (plen p))) } 
  @-}
liquid_thm_ptr_cmp :: Ptr a -> Ptr a -> Ptr a
liquid_thm_ptr_cmp p q = undefined -- p -- LIQUID : make this undefined to suppress WARNING

{-@ liquid_thm_ptr_cmp' :: p:PtrV a 
                        -> q:{v:(PtrV a) | ((plen v) >= (plen p) && v != p && (pbase v) = (pbase p))} 
                        -> {v: (PtrV a)  | ((v = p) && ((plen v) > 0) && ((plen q) > (plen p))) } 
  @-}
liquid_thm_ptr_cmp' :: Ptr a -> Ptr a -> Ptr a
liquid_thm_ptr_cmp' p q = undefined 


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



-- -----------------------------------------------------------------------------

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


{-@ foldl1 :: (Word8 -> Word8 -> Word8) -> ByteStringNE -> Word8 @-}
foldl1 :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldl1 = undefined

-- | 'foldl1\'' is like 'foldl1', but strict in the accumulator.
-- An exception will be thrown in the case of an empty ByteString.
{-@ foldl1' :: (Word8 -> Word8 -> Word8) -> ByteStringNE -> Word8 @-}
foldl1' :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldl1' = undefined

{-@ null :: b:ByteString -> {v:Bool | ((Prop v) <=> ((bLength b) = 0))} @-}
null :: ByteString -> Bool
null = undefined 

{- foldl :: (a -> Word8 -> a) -> a -> ByteString -> a @-}
-- foldl :: (a -> Word8 -> a) -> a -> ByteString -> a
-- foldl = undefined

{- foldl' :: (a -> Word8 -> a) -> a -> ByteString -> a @-}
-- foldl' :: (a -> Word8 -> a) -> a -> ByteString -> a
-- foldl' = undefined

{-@ empty :: {v:ByteString | (bLength v) = 0} @-} 
empty :: ByteString
empty = undefined

{-@ length :: b:ByteString -> {v:Nat | v = (bLength b)} @-}
length :: ByteString -> Int
length = undefined

{-@ append :: b1:ByteString -> b2:ByteString -> {v:ByteString | (bLength v) = (bLength b1) + (bLength b2)} @-}
append :: ByteString -> ByteString -> ByteString
append = undefined

{-@ concat :: bs:[ByteString] -> {v:ByteString | (bLength v) = (bLengths bs)} @-}
concat :: [ByteString] -> ByteString
concat = undefined

{-@ lengths :: bs:[ByteString] -> {v:Nat | v = (bLengths bs)} @-}
lengths :: [ByteString] -> Int
lengths []     = 0
lengths (b:bs) = length b + lengths bs

{-@ snoc :: b:ByteString -> Word8 -> {v:ByteStringNE | (bLength v) = 1 + (bLength b)} @-}
snoc :: ByteString -> Word8 -> ByteString
snoc = undefined

{-@ last :: ByteStringNE -> Word8 @-}
last :: ByteString -> Word8
last = undefined

{-@ cons :: Word8 -> b:ByteString -> {v:ByteString | (bLength v) = 1 + (bLength b)} @-}
cons :: Word8 -> ByteString -> ByteString
cons = undefined

{-@ init :: b:ByteStringNE -> {v:ByteString | (bLength v) = (bLength b) - 1} @-}
init :: ByteString -> ByteString
init = undefined

{-@ takeWhile :: (Word8 -> Bool) -> b:ByteString -> (ByteStringLE b) @-}
takeWhile :: (Word8 -> Bool) -> ByteString -> ByteString
takeWhile f ps = undefined 
{-# INLINE takeWhile #-}

-- | 'dropWhile' @p xs@ returns the suffix remaining after 'takeWhile' @p xs@.
{-@ dropWhile :: (Word8 -> Bool) -> b:ByteString -> (ByteStringLE b) @-}
dropWhile :: (Word8 -> Bool) -> ByteString -> ByteString
dropWhile f ps = undefined

-- | 'break' @p@ is equivalent to @'span' ('not' . p)@.
{-@ break :: (Word8 -> Bool) -> b:ByteString -> (ByteStringPair b) @-}
break :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
break p ps = undefined


{-@ breakByte :: Word8 -> b:ByteString -> (ByteStringPair b) @-}
breakByte :: Word8 -> ByteString -> (ByteString, ByteString)
breakByte = undefined

{-@ findIndexOrEnd :: (Word8 -> Bool) -> b:ByteString -> {v:Nat | v <= (bLength b) } @-}
findIndexOrEnd :: (Word8 -> Bool) -> ByteString -> Int
findIndexOrEnd = undefined

{-@ elemIndex :: Word8 -> b:ByteString -> Maybe {v:Nat | v < (bLength b)} @-}
elemIndex :: Word8 -> ByteString -> Maybe Int
elemIndex = undefined

-- LIQUID HACK: this is to get all the quals from memchr. Quals needed because IO monad forces liquid-abstraction. Solution, scrape quals from predicate defs (e.g. SuffixPtr)
{-@ memchrDUMMYFORQUALS :: p:(Ptr a) -> n:Int -> (IO {v:(Ptr b) | (SuffixPtr v n p)})  @-}
memchrDUMMYFORQUALS :: Ptr a -> Int -> IO (Ptr b)
memchrDUMMYFORQUALS = undefined 

{-@ splitAt :: n:Int
            -> b:ByteString
            -> ({v:ByteString | (Min (bLength v) (bLength b)
                                     (if (n >= 0) then n else 0))}
               , ByteString)<{\x y -> (bLength y) = ((bLength b) - (bLength x))}>
  @-}
splitAt :: Int -> ByteString -> (ByteString, ByteString)
splitAt = undefined

{-@ findFromEndUntil :: (Word8 -> Bool) -> b:ByteString -> {v:Nat | v <= (bLength b) } @-}
findFromEndUntil :: (Word8 -> Bool) -> ByteString -> Int
findFromEndUntil = undefined

{-@ breakEnd :: (Word8 -> Bool) -> b:ByteString -> (ByteStringPair b) @-}
breakEnd :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
breakEnd = undefined

{-@ span :: (Word8 -> Bool) -> b:ByteString -> (ByteStringPair b) @-}
span :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
span = undefined 

{-@ spanByte :: Word8 -> b:ByteString -> (ByteStringPair b) @-}
spanByte :: Word8 -> ByteString -> (ByteString, ByteString)
spanByte = undefined

{-@ spanEnd :: (Word8 -> Bool) -> b:ByteString -> (ByteStringPair b) @-}
spanEnd :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
spanEnd = undefined

{-@ count :: Word8 -> b:ByteString -> {v:Nat | v <= (bLength b) } @-}
count :: Word8 -> ByteString -> Int
count = undefined

{-@ replicate :: n:Nat -> Word8 -> {v:ByteString | (bLength v) = (if n > 0 then n else 0)} @-}
replicate :: Int -> Word8 -> ByteString
replicate  = undefined

{- findIndex :: (Word8 -> Bool) -> b:ByteString -> (Maybe {v:Nat | v < (bLength b)}) @-}
-- findIndex :: (Word8 -> Bool) -> ByteString -> Maybe Int
-- findIndex = undefined

{- filter :: (Word8 -> Bool) -> b:ByteString -> (ByteStringLE b) @-}
-- filter :: (Word8 -> Bool) -> ByteString -> ByteString
-- filter = undefined

{-@ isPrefixOf :: ByteString -> ByteString -> Bool @-}
isPrefixOf :: ByteString -> ByteString -> Bool 
isPrefixOf = undefined

{-@ take :: n:Nat -> b:ByteString -> {v:ByteString | (bLength v) = (if (n <= (bLength b)) then n else (bLength b))} @-}
take :: Int -> ByteString -> ByteString
take = undefined

{-@ singleton :: Word8 -> {v:ByteString | (bLength v) = 1} @-}
singleton :: Word8 -> ByteString
singleton = undefined


hPut :: Handle -> ByteString -> IO ()
hPut = undefined

{-@ hGet :: Handle -> n:Nat -> IO {v:ByteString | (bLength v) <= n} @-}
hGet :: Handle -> Int -> IO ByteString
hGet = undefined

{-@ pack :: cs:[Word8] -> {v:ByteString | (bLength v) = (len cs)} @-}
pack :: [Word8] -> ByteString
pack = undefined

{-@ unpack :: b:ByteString -> {v:[Word8] | (len v) = (bLength b)} @-}
-- unpack :: ByteString -> [Word8]
-- unpack = undefined

unpackFoldr :: ByteString -> (Word8 -> a -> a) -> a -> a
unpackFoldr = undefined


------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------

{-@ qualif FindIndices(v:Data.ByteString.Internal.ByteString,
                       p:Data.ByteString.Internal.ByteString,
                       n:Int):
        (bLength v) = (bLength p) - n  @-}

-- LIQUID NICE-INFERENCE-EXAMPLE! But screws up everyone else's type. Yuck. 
{-@ predicate ZipLenB V X Y = (bLength V) = (if (bLength X) <= (bLength Y) then (bLength X) else (bLength Y)) @-}
{-@ zipWith' :: (Word8 -> Word8 -> Word8) -> x:ByteString -> y:ByteString -> {v:ByteString | (ZipLenB v x y)} @-}
zipWith' :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString -> ByteString
zipWith' f (PS fp s l) (PS fq t m) = inlinePerformIO $
    withForeignPtr fp $ \a ->
    withForeignPtr fq $ \b ->
    create len $ zipWith_ len 0 (a `plusPtr` s) (b `plusPtr` t)
  where
    zipWith_ :: Int -> Int -> Ptr Word8 -> Ptr Word8 -> Ptr Word8 -> IO ()
    STRICT5(zipWith_)
    zipWith_ (d::Int) n p1 p2 r -- LIQUID TERMINATION
       | n >= len = return ()
       | otherwise = do
            x <- peekByteOff p1 n
            y <- peekByteOff p2 n
            pokeByteOff r n (f x y)
            zipWith_ (d-1) (n+1) p1 p2 r

    len = min l m



{-@ qualif FilterLoop(v:GHC.Ptr.Ptr a, f:GHC.Ptr.Ptr a, t:GHC.Ptr.Ptr a):
        (plen t) >= (plen f) - (plen v) @-}
{-@ filter :: (Word8 -> Bool) -> b:ByteString -> (ByteStringLE b) @-}
filter :: (Word8 -> Bool) -> ByteString -> ByteString
filter k ps@(PS x s l)
    | null ps   = ps
    | otherwise = unsafePerformIO $ createAndTrim l $ \p -> withForeignPtr x $ \f -> do
        t <- go l (f `plusPtr` s) p (f `plusPtr` (s + l))
        return $! t `minusPtr` p -- actual length
    where
      STRICT4(go)
      go (d::Int) f' t end 
                  | f' == end = return t
                  | otherwise = do
                        let f = liquid_thm_ptr_cmp f' end
                        w <- peek f
                        if k w
                          then poke t w >> go (d-1) (f `plusPtr` 1) (t `plusPtr` 1) end
                          else             go (d-1) (f `plusPtr` 1) t               end


