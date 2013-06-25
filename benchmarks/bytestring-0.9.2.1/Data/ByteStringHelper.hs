{-# OPTIONS_GHC -cpp -fglasgow-exts -fno-warn-orphans #-}

module Data.ByteStringHelper where

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

-- -----------------------------------------------------------------------------
-- for splitWith
{-@ qualif SplitWith(v:List ByteString, l:Int): ((bLengths v) + (len v) - 1) = l @-}

-- for split
{-@ qualif BSValidOff(v:Int,l:Int,p:ForeignPtr a): v + l <= (fplen p) @-}
{-@ qualif SplitLoop(v:List ByteString, l:Int, n:Int): (bLengths v) + (len v) - 1 = l - n @-}
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

{-@ foldl :: (a -> Word8 -> a) -> a -> ByteString -> a @-}
foldl :: (a -> Word8 -> a) -> a -> ByteString -> a
foldl = undefined

{-@ foldl' :: (a -> Word8 -> a) -> a -> ByteString -> a @-}
foldl' :: (a -> Word8 -> a) -> a -> ByteString -> a
foldl' = undefined

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

{-@ splitAt :: Int -> b:ByteString -> (ByteStringPair b) @-}
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

------------------------------------------------------------------------------------
------------------------------------------------------------------------------------
------------------------------------------------------------------------------------
------------------------------------------------------------------------------------
------------------------------------------------------------------------------------


{-@ splitWith :: (Word8 -> Bool) -> b:ByteStringNE -> (ByteStringSplit b) @-}
splitWith _pred (PS _  _   0) = [empty]
splitWith pred_ (PS fp off len) = splitWith0 pred# off len fp
  where pred# c# = pred_ (W8# c#)

        STRICT4(splitWith0)
        splitWith0 pred' off' len' fp' = withPtr fp $ \p ->
            splitLoop pred' p 0 off' len' fp'

        splitLoop :: (Word# -> Bool)
                  -> Ptr Word8
                  -> Int -> Int -> Int
                  -> ForeignPtr Word8
                  -> IO [ByteString]

        splitLoop pred' p idx' off' len' fp'
            | pred' `seq` p `seq` idx' `seq` off' `seq` len' `seq` fp' `seq` False = undefined
            | idx' >= len'  = return [PS fp' off' idx']
            | otherwise = do
                w <- peekElemOff p (off'+idx')
                if pred' (case w of W8# w# -> w#)
                   then return (PS fp' off' idx' :
                              splitWith0 pred' (off'+idx'+1) (len'-idx'-1) fp')
                   else splitLoop pred' p (idx'+1) off' len' fp'

---------------------------------------------------------------------------------------------------
--- MAY AS WELL KEEP THeSE AROUND!
---------------------------------------------------------------------------------------------------

{-@ splitO :: Word8 -> b:ByteStringNE -> (ByteStringSplit b)  @-}
splitO _ (PS _ _ 0) = []
splitO w (PS xanadu s l) = inlinePerformIO $ withForeignPtr xanadu $ \pz -> do
    let p   = liquidAssert (fpLen xanadu == pLen pz) pz
    let ptrGOBBLE_ = p `plusPtr` s
    let ptrGOBBLE  = liquidAssert (l <= pLen ptrGOBBLE_) ptrGOBBLE_ 
    return (splitLoop xanadu ptrGOBBLE w l s 0)


{-@ splitLoop :: fp:(ForeignPtr Word8) 
          -> p:(Ptr Word8) 
          -> Word8 
          -> l:{v:Nat | v <= (plen p)} 
          -> s:{v:Nat | v + l <= (fplen fp)}
          -> n:{v:Nat | v <= l} 
          -> {v:[ByteString] | (bLengths v) + (len v) - 1 = l - n} 
  @-}
splitLoop :: ForeignPtr Word8 -> Ptr Word8 -> Word8 -> Int -> Int -> Int -> [ByteString]
splitLoop xanadu ptrGOBBLE w l s n = 
  let ptrn = ((ptrGOBBLE `plusPtr` n) :: Ptr Word8) 
           -- NEEDED: else lose `plen` information without cast
           -- thanks to subsequent @ Word8 application
      q    = inlinePerformIO $ memchr ptrn w (fromIntegral (l-n))
  in if isNullPtr q {- LIQUID q == nullPtr -}
       then [PS xanadu (s+n) (l-n)]
       else let i' = q `minusPtr` ptrGOBBLE
                i  = liquidAssert (n <= i' && i' < l) i'
            in PS xanadu (s+n) (i-n) : splitLoop xanadu ptrGOBBLE w l s (i+1)

 
---------------------------------------------------------------------------------------------------


{-@ split :: Word8 -> b:ByteStringNE -> (ByteStringSplit b)  @-}
split :: Word8 -> ByteString -> [ByteString]
split _ (PS _ _ 0) = []
split w (PS x s l) = inlinePerformIO $ withForeignPtr x $ \p -> do
    let ptr = p `plusPtr` s

        STRICT1(loop)
        loop n =
            -- LIQUID: else lose `plen` info due to subsequent @ Word8 application
            let ptrn = (ptr `plusPtr` n) :: Ptr Word8 
                q = inlinePerformIO $ memchr ptrn {- (ptr `plusPtr` n) -}
                                           w (fromIntegral (l-n))
            in if isNullPtr q {- LIQUID q == nullPtr -}
                then [PS x (s+n) (l-n)]
                else let i = q `minusPtr` ptr in PS x (s+n) (i-n) : loop (i+1)

    return (loop 0)
{-# INLINE split #-}

---------------------------------------------------------------
---------------------------------------------------------------
---------------------------------------------------------------
---------------------------------------------------------------
---------------------------------------------------------------
------------------- HEREHEREHEREHEREHERE ----------------------
------------------- HEREHEREHEREHEREHERE ----------------------
------------------- HEREHEREHEREHEREHERE ----------------------
---------------------------------------------------------------
---------------------------------------------------------------
---------------------------------------------------------------
---------------------------------------------------------------
---------------------------------------------------------------

-- | The 'group' function takes a ByteString and returns a list of
-- ByteStrings such that the concatenation of the result is equal to the
-- argument.  Moreover, each sublist in the result contains only equal
-- elements.  For example,
--
-- > group "Mississippi" = ["M","i","ss","i","ss","i","pp","i"]
--
-- It is a special case of 'groupBy', which allows the programmer to
-- supply their own equality test. It is about 40% faster than 
-- /groupBy (==)/
group :: ByteString -> [ByteString]
group xs
    | null xs   = []
    | otherwise = ys : group zs
    where
        (ys, zs) = spanByte (unsafeHead xs) xs

-- | The 'groupBy' function is the non-overloaded version of 'group'.
groupBy :: (Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]
groupBy k xs
    | null xs   = []
    | otherwise = unsafeTake n xs : groupBy k (unsafeDrop n xs)
    where
        n = 1 + findIndexOrEnd (not . k (unsafeHead xs)) (unsafeTail xs)























