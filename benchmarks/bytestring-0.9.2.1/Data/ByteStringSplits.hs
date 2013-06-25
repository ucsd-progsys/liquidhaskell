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

-- LIQUID: This will go away when we properly embed Ptr a as int -- only in
-- fixpoint to avoid the Sort mismatch hassles. 
{-@ liquid_thm_ptr_cmp :: p:PtrV a 
                       -> q:{v:(PtrV a) | ((plen v) <= (plen p) && v != p && (pbase v) = (pbase p))} 
                       -> {v: (PtrV a)  | ((v = p) && ((plen q) < (plen p))) } 
  @-}
liquid_thm_ptr_cmp :: Ptr a -> Ptr a -> Ptr a
liquid_thm_ptr_cmp p q = undefined -- p -- LIQUID : make this undefined to suppress WARNING

-- -----------------------------------------------------------------------------
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


{-@ replicate :: n:Nat -> Word8 -> {v:ByteString | (bLength v) = (if n > 0 then n else 0)} @-}
replicate :: Int -> Word8 -> ByteString
replicate  = undefined

-----------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------

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

{-@ splitO :: Word8 -> b:ByteStringNE -> (ByteStringSplit b)  @-}
splitO :: Word8 -> ByteString -> [ByteString]
splitO _ (PS _ _ 0) = []
splitO w (PS x s l) = inlinePerformIO $ withForeignPtr x $ \p -> do
    let ptr = p `plusPtr` s
    return (splitLoop x ptr w l s 0)

-- LIQUID TODO: THIS ORIGINAL CODE WORKS FINE IN ISOLATION BUT SOMEHOW BREAKS ON LARGE FILE. 
-- TOO SICK AND TIRED TO INVESTIGATE WTF is going on...
--         STRICT1(loop)
--         loop n =
--             -- LIQUID: else lose `plen` info due to subsequent @ Word8 application
--             let ptrn = (ptr `plusPtr` n) :: Ptr Word8 
--                 q = inlinePerformIO $ memchr ptrn {- (ptr `plusPtr` n) -}
--                                            w (fromIntegral (l-n))
--             in if isNullPtr q {- LIQUID q == nullPtr -}
--                 then [PS x (s+n) (l-n)]
--                 else let i = q `minusPtr` ptr in PS x (s+n) (i-n) : loop (i+1)
-- 
--     return (loop 0)


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

{-@ splitWith :: (Word8 -> Bool) -> b:ByteStringNE -> (ByteStringSplit b) @-}
splitWith :: (Word8 -> Bool) -> ByteString -> [ByteString]

splitWith _pred (PS _  _   0) = []
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
{-# INLINE splitWith #-}



{-@ group :: b:ByteString -> {v: [ByteString] | (bLengths v) = (bLength b)} @-}
group :: ByteString -> [ByteString]
group xs
    | null xs   = []
    | otherwise = let (ys, zs) = spanByte (unsafeHead xs) xs in 
                  ys : group zs
    -- LIQUID LAZY: where
    -- LIQUID LAZY:     (ys, zs) = spanByte (unsafeHead xs) xs

{-@ groupBy :: (Word8 -> Word8 -> Bool) -> b:ByteString -> {v:[ByteString] | (bLengths v) = (bLength b)} @-}
groupBy :: (Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]
groupBy k xs
    | null xs   = []
    | otherwise = let n = 1 + findIndexOrEnd (not . k (unsafeHead xs)) (unsafeTail xs) in
                  unsafeTake n xs : groupBy k (unsafeDrop n xs)
    -- LIQUID LAZY: where
    -- LIQUID LAZY:     n = 1 + findIndexOrEnd (not . k (unsafeHead xs)) (unsafeTail xs)

{-@ inits :: b:ByteString -> {v:[{v1:ByteString | (bLength v1) <= (bLength b)}] | (len v) = 1 + (bLength b)} @-}
inits :: ByteString -> [ByteString]
inits (PS x s l) = [PS x s n | n <- rng l {- LIQUID COMPREHENSIONS [0..l] -}]

{-@ rng :: n:Nat -> {v:[{v1:Nat | v1 <= n }] | (len v) = n + 1} @-}
rng :: Int -> [Int]
rng 0 = [0]
rng n = n : rng (n-1) 

{-@ tails :: b:ByteString -> {v:[{v1:ByteString | (bLength v1) <= (bLength b)}] | (len v) = 1 + (bLength b)} @-}
tails :: ByteString -> [ByteString]
tails p | null p    = [empty]
        | otherwise = p : tails (unsafeTail p)


{-@ index :: b:ByteString -> {v:Nat | v < (bLength b)} -> Word8 @-}
index :: ByteString -> Int -> Word8
index ps n
    | n < 0          = moduleError "index" ("negative index: " ++ show n)
    | n >= length ps = moduleError "index" ("index too large: " ++ show n
                                         ++ ", length = " ++ show (length ps))
    | otherwise      = ps `unsafeIndex` n


{-@ elemIndexEnd :: Word8 -> b:ByteString -> Maybe {v:Nat | v < (bLength b) } @-}
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


{-@ elemIndices :: Word8 -> b:ByteString -> [{v:Nat | v < (bLength b) }] @-}
elemIndices :: Word8 -> ByteString -> [Int]
elemIndices w (PS x s l) = inlinePerformIO $ withForeignPtr x $ \p -> do
    let ptr = p `plusPtr` s

        STRICT1(loop)
        loop n = let pn = ((ptr `plusPtr` n) :: Ptr Word8)
                     q  = inlinePerformIO $ memchr pn
                                                 w (fromIntegral (l - n))
                 in if isNullPtr q {- == nullPtr -}
                        then []
                        else let i = q `minusPtr` ptr
                             in i : loop (i+1)
    return $! loop 0

{-@ count :: Word8 -> b:ByteString -> {v:Nat | v <= (bLength b) } @-}
count :: Word8 -> ByteString -> Int
count w (PS x s m) = inlinePerformIO $ withForeignPtr x $ \p ->
    fmap fromIntegral $ c_count (p `plusPtr` s) (fromIntegral m) w

{-@ findIndex :: (Word8 -> Bool) -> b:ByteString -> (Maybe {v:Nat | v < (bLength b)}) @-}
findIndex :: (Word8 -> Bool) -> ByteString -> Maybe Int
findIndex k (PS x s l) = inlinePerformIO $ withForeignPtr x $ \f -> go (f `plusPtr` s) 0
  where
    STRICT2(go)
    go ptr n | n >= l    = return Nothing
             | otherwise = do w <- peek ptr
                              if k w
                                then return (Just n)
                                else go (ptr `plusPtr` 1) (n+1)

{-@ qualif FindIndices(v:ByteString, p:ByteString, n:Int) : (bLength v) = (bLength p) - n 
  @-}

{-@ findIndices :: (Word8 -> Bool) -> b:ByteString -> [{v:Nat | v < (bLength b)}] @-}
findIndices :: (Word8 -> Bool) -> ByteString -> [Int]
findIndices p ps = loop 0 ps
   where
     STRICT2(loop)
     loop (n :: Int) qs 
        | null qs           = []
        | p (unsafeHead qs) = n : loop (n+1) (unsafeTail qs)
        | otherwise         =     loop (n+1) (unsafeTail qs)

elem :: Word8 -> ByteString -> Bool
elem c ps = case elemIndex c ps of Nothing -> False ; _ -> True
{-# INLINE elem #-}

notElem :: Word8 -> ByteString -> Bool
notElem c ps = not (elem c ps)
{-# INLINE notElem #-}


{-@ qualif FilterLoop(v:Ptr a, f:Ptr a, t:Ptr a): (plen t) >= (plen f) - (plen v) @-}
{-@ filter :: (Word8 -> Bool) -> b:ByteString -> (ByteStringLE b) @-}
filter :: (Word8 -> Bool) -> ByteString -> ByteString
filter k ps@(PS x s l)
    | null ps   = ps
    | otherwise = unsafePerformIO $ createAndTrim l $ \p -> withForeignPtr x $ \f -> do
        t <- go (f `plusPtr` s) p (f `plusPtr` (s + l))
        return $! t `minusPtr` p -- actual length
    where
      STRICT3(go)
      go f' t end | f' == end = return t
                  | otherwise = do
                        let f = liquid_thm_ptr_cmp f' end
                        w <- peek f
                        if k w
                          then poke t w >> go (f `plusPtr` 1) (t `plusPtr` 1) end
                          else             go (f `plusPtr` 1) t               end


{- goFilterLoop :: (Word8 -> Bool) 
       -> f:(PtrV Word8) 
       -> t:(PtrV Word8)
       -> e:{v:(PtrV Word8) | ((pbase v) = (pbase f) && (plen v) <= (plen f) && (plen t) >= (plen f) - (plen v)) } 
       -> (IO {v: (PtrV Word8) | ((pbase v) = (pbase t) && (plen v) <= (plen t))}) @-}
-- goFilterLoop :: (Word8 -> Bool) -> (Ptr Word8) -> (Ptr Word8) -> Ptr Word8 -> IO (Ptr Word8)
-- goFilterLoop k f' t end 
--   | f' == end = return t
--   | otherwise = do
--                   let f = liquid_thm_ptr_cmp f' end
--                   w <- peek f
--                   if k w
--                     then poke t w >> goFilterLoop k (f `plusPtr` 1) (t `plusPtr` 1) end
--                     else             goFilterLoop k (f `plusPtr` 1) t               end


{-@ filterByte :: Word8 -> b:ByteString -> {v:ByteString | (bLength v) <= (bLength b)} @-}
filterByte :: Word8 -> ByteString -> ByteString
filterByte w ps = replicate (count w ps) w


find :: (Word8 -> Bool) -> ByteString -> Maybe Word8
find f p = case findIndex f p of
                    Just n -> Just (p `unsafeIndex` n)
                    _      -> Nothing


{-@ partition :: (Word8 -> Bool) -> b:ByteString -> ((ByteStringLE b), (ByteStringLE b)) @-}
partition :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
partition p bs = (filter p bs, filter (not . p) bs)


{-@ isPrefixOf :: ByteString -> ByteString -> Bool @-}
isPrefixOf :: ByteString -> ByteString -> Bool 
isPrefixOf (PS x1 s1 l1) (PS x2 s2 l2)
    | l1 == 0   = True
    | l2 < l1   = False
    | otherwise = inlinePerformIO $ withForeignPtr x1 $ \p1 ->
        withForeignPtr x2 $ \p2 -> do
            i <- memcmp (p1 `plusPtr` s1) (p2 `plusPtr` s2) (fromIntegral l1)
            return $! i == 0


{-@ isSuffixOf :: ByteString -> ByteString -> Bool @-}
isSuffixOf :: ByteString -> ByteString -> Bool
isSuffixOf (PS x1 s1 l1) (PS x2 s2 l2)
    | l1 == 0   = True
    | l2 < l1   = False
    | otherwise = inlinePerformIO $ withForeignPtr x1 $ \p1 ->
        withForeignPtr x2 $ \p2 -> do
            i <- memcmp (p1 `plusPtr` s1) (p2 `plusPtr` s2 `plusPtr` (l2 - l1)) (fromIntegral l1)
            return $! i == 0

