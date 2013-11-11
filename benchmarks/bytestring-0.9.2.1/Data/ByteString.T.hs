{-# OPTIONS_GHC -cpp -fglasgow-exts -fno-warn-orphans #-}

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
import Language.Haskell.Liquid.Prelude hiding (eq) 
import Language.Haskell.Liquid.Foreign

{-@ include <ByteString.hs.hquals> @-}

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

{- qualif Zog(v:a, p:a)         : (plen p) <= (plen v)          @-}
{- qualif Zog(v:a)              : 0 <= (plen v)                 @-}

-- for unfoldrN 
{- qualif PtrDiffUnfoldrN(v:int, i:int, p:Ptr a): (i - v) <= (plen p) @-}

{-@ lengths :: bs:[ByteString] -> {v:Nat | v = (bLengths bs)} @-}
lengths :: [ByteString] -> Int
lengths []     = 0
lengths (b:bs) = length b + lengths bs

-- LIQUID HACK: this is to get all the quals from memchr. 
-- Quals needed because IO monad forces liquid-abstraction. 
-- Solution, scrape quals from predicate defs (e.g. SuffixPtr)
{-@ dummyForQuals1_elemIndex :: p:(Ptr Word8) -> n:Int -> (IO {v:(Ptr Word8) | (SuffixPtr v n p)})  @-}
dummyForQuals1_elemIndex :: Ptr Word8 -> Int -> IO (Ptr Word8)
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

-- -----------------------------------------------------------------------------

instance Eq  ByteString
    where (==)    = eq

instance Ord ByteString
  where compare = compareBytes

-- LIQUID instance Monoid ByteString where
-- LIQUID     mempty  = empty
-- LIQUID     mappend = append
-- LIQUID     mconcat = concat

{-
instance Arbitrary PackedString where
    arbitrary = P.pack `fmap` arbitrary
    coarbitrary s = coarbitrary (P.unpack s)
-}

-- | /O(n)/ Equality on the 'ByteString' type.
{-@ eq :: ByteString -> ByteString -> Bool @-}
eq :: ByteString -> ByteString -> Bool
eq a@(PS p s l) b@(PS p' s' l')
    | l /= l'            = False    -- short cut on length
    | p == p' && s == s' = True     -- short cut for the same string
    | otherwise          = compareBytes a b == EQ
{-# INLINE eq #-}

-- | /O(n)/ 'compareBytes' provides an 'Ordering' for 'ByteStrings' supporting slices. 
compareBytes :: ByteString -> ByteString -> Ordering
compareBytes (PS x1 s1 l1) (PS x2 s2 l2)
    | l1 == 0  && l2 == 0               = EQ  -- short cut for empty strings
    | x1 == x2 && s1 == s2 && l1 == l2  = EQ  -- short cut for the same string
    | otherwise                         = inlinePerformIO $
        withForeignPtr x1 $ \p1 ->
        withForeignPtr x2 $ \p2 -> do
            i <- memcmp (p1 `plusPtr` s1) (p2 `plusPtr` s2) (fromIntegral $ min l1 l2)
            return $! case i `compare` 0 of
                        EQ  -> l1 `compare` l2
                        x   -> x
{-# INLINE compareBytes #-}

 
{-
--
-- About 4x slower over 32M
--
compareBytes :: ByteString -> ByteString -> Ordering
compareBytes (PS fp1 off1 len1) (PS fp2 off2 len2) = inlinePerformIO $
    withForeignPtr fp1 $ \p1 ->
        withForeignPtr fp2 $ \p2 ->
            cmp (p1 `plusPtr` off1)
                (p2 `plusPtr` off2) 0 len1 len2

cmp :: Ptr Word8 -> Ptr Word8 -> Int -> Int -> Int-> IO Ordering
STRICT5(cmp)
cmp p1 p2 n len1 len2
      | n == len1 = if n == len2 then return EQ else return LT
      | n == len2 = return GT
      | otherwise = do
          (a :: Word8) <- peekByteOff p1 n
          (b :: Word8) <- peekByteOff p2 n
          case a `compare` b of
                EQ -> cmp p1 p2 (n+1) len1 len2
                LT -> return LT
                GT -> return GT
{-# INLINE compareBytes #-}
-}

-- -----------------------------------------------------------------------------
-- Introducing and eliminating 'ByteString's

-- | /O(1)/ The empty 'ByteString'
{-@ empty :: {v:ByteString | (bLength v) = 0} @-} 
empty :: ByteString
empty = PS nullForeignPtr 0 0

 
-- | /O(1)/ Convert a 'Word8' into a 'ByteString'

{-@ singleton :: Word8 -> {v:ByteString | (bLength v) = 1} @-}
singleton :: Word8 -> ByteString
singleton c = unsafeCreate 1 $ \p -> poke p c
{-# INLINE [1] singleton #-}

--
-- XXX The unsafePerformIO is critical!
--
-- Otherwise:
--
--  singleton 255 `compare` singleton 127
--
-- is compiled to:
--
--  case mallocByteString 2 of 
--      ForeignPtr f internals -> 
--           case writeWord8OffAddr# f 0 255 of _ -> 
--           case writeWord8OffAddr# f 0 127 of _ ->
--           case eqAddr# f f of 
--                  False -> case compare (GHC.Prim.plusAddr# f 0) 
--                                        (GHC.Prim.plusAddr# f 0)
--
--

-- | /O(n)/ Convert a '[Word8]' into a 'ByteString'. 
--
-- For applications with large numbers of string literals, pack can be a
-- bottleneck. In such cases, consider using packAddress (GHC only).
{-@ pack :: cs:[Word8] -> {v:ByteString | (bLength v) = (len cs)} @-}
pack :: [Word8] -> ByteString

#if !defined(__GLASGOW_HASKELL__)

pack str = unsafeCreate (P.length str) $ \p -> go p str
    where
        go _ []     = return ()
        go p (x:xs) = poke p x >> go (p `plusPtr` 1) xs -- less space than pokeElemOff

#else /* hack away */

pack str = unsafeCreate (P.length str) $ \(Ptr p) -> stToIO (go_pack p 0# str)
    where
        {-@ Decrease go_pack 3 @-}
        go_pack _ _ []         = return ()
        go_pack p i (W8# c:cs) = writeByte p i c >> go_pack p (i +# 1#) cs

        writeByte p i c = ST $ \s# ->
            case writeWord8OffAddr# p i c s# of s2# -> (# s2#, () #)
#endif


-- | /O(n)/ Converts a 'ByteString' to a '[Word8]'.
{-@ unpack :: b:ByteString -> {v:[Word8] | (len v) = (bLength b)} @-}
unpack :: ByteString -> [Word8]

#if !defined(__GLASGOW_HASKELL__)
unpack (PS _  _ 0) = []
unpack (PS ps s l) = inlinePerformIO $ withForeignPtr ps $ \p ->
        go (p `plusPtr` s) (l - 1) []
    where
        STRICT3(go)
        go p 0 acc = peek p          >>= \e -> return (e : acc)
        go p n acc = peekByteOff p n >>= \e -> go p (n-1) (e : acc)
{-# INLINE unpack #-}

#else

-- unpack ps = build (unpackFoldr ps)

-- LIQUID TODO unpackFoldr :: forall <p :: Int -> a -> Prop>. 
--                   b:ByteString 
--                -> (i:Int -> Word8 -> a<p i> -> a<p (i+1)>)
--                -> (a<p 0>)
--                -> (a<p (bLength b)>)
{-# INLINE unpack #-}

-- LIQUID INLINED : unpack ps = build (unpackFoldr ps) = unpackFoldr ps (:) [] 
-- LIQUID INLINED : so inline `f` with `:` and `ch` with `[]`
unpack ps  = unpackFoldrINLINED ps

unpackFoldrINLINED :: ByteString -> [Word8]
unpackFoldrINLINED (PS fp off len) = withPtr fp $ \p -> do
    let loop _ q n    _   | q `seq` n `seq` False = undefined -- n.b.
        loop _ _ (-1) acc = return acc
    {- LIQUID WITNESS -}
        loop (d::Int) q n    acc = do
           a <- peekByteOff q n
           loop (d-1) q (n-1) (a : acc)
    loop len (p `plusPtr` off) (len-1) [] 



-- critical this isn't strict in the acc
-- as it will break in the presence of list fusion. this is a known
-- issue with seq and build/foldr rewrite rules, which rely on lazy
-- demanding to avoid bottoms in the list.
--
unpackFoldr :: ByteString -> (Word8 -> a -> a) -> a -> a
unpackFoldr (PS fp off len) f ch = withPtr fp $ \p -> do
    let loop _ q n    _   | q `seq` n `seq` False = undefined -- n.b.
        loop _ _ (-1) acc = return acc
  {- LIQUID WITNESS -}
        loop (d :: Int) q n    acc = do
           a <- peekByteOff q n
           loop (d-1) q (n-1) (a `f` acc)
    loop len (p `plusPtr` off) (len-1) ch
{-# INLINE [0] unpackFoldr #-}

{-@ unpackList :: b:ByteString -> {v:[Word8] | (len v) = (bLength b)} @-}
unpackList :: ByteString -> [Word8]
unpackList (PS fp off len) = withPtr fp $ \p -> do
    let STRICT4(loop)
        loop _ _ (-1) acc = return acc
  {- LIQUID WITNESS -}
        loop (d::Int) q n acc = do
           a <- peekByteOff q n
           loop (d-1) q (n-1) (a : acc)
    loop len (p `plusPtr` off) (len-1) []

{-# RULES
    "FPS unpack-list"  [1]  forall p  . unpackFoldr p (:) [] = unpackList p
 #-}

#endif

-- ---------------------------------------------------------------------
-- Basic interface

-- | /O(1)/ Test whether a ByteString is empty.
{-@ null :: b:ByteString -> {v:Bool | ((Prop v) <=> ((bLength b) = 0))} @-}
null :: ByteString -> Bool
null (PS _ _ l) = assert (l >= 0) $ l <= 0
{-# INLINE null #-}

-- ---------------------------------------------------------------------
-- | /O(1)/ 'length' returns the length of a ByteString as an 'Int'.
{-@ length :: b:ByteString -> {v:Nat | v = (bLength b)} @-}
length :: ByteString -> Int
length (PS _ _ l) = assert (l >= 0) $ l
{-# INLINE length #-}

------------------------------------------------------------------------

-- | /O(n)/ 'cons' is analogous to (:) for lists, but of different
-- complexity, as it requires a memcpy.

{-@ cons :: Word8 -> b:ByteString -> {v:ByteString | (bLength v) = 1 + (bLength b)} @-}
cons :: Word8 -> ByteString -> ByteString
cons c (PS x s l) = unsafeCreate (l+1) $ \p -> withForeignPtr x $ \f -> do
        poke p c
        memcpy (p `plusPtr` 1) (f `plusPtr` s) (fromIntegral l)
{-# INLINE cons #-}

-- | /O(n)/ Append a byte to the end of a 'ByteString'
{-@ snoc :: b:ByteString -> Word8 -> {v:ByteString | (bLength v) = 1 + (bLength b)} @-}
snoc :: ByteString -> Word8 -> ByteString
snoc (PS x s l) c = unsafeCreate (l+1) $ \p -> withForeignPtr x $ \f -> do
        memcpy p (f `plusPtr` s) (fromIntegral l)
        poke (p `plusPtr` l) c
{-# INLINE snoc #-}

-- todo fuse

-- | /O(1)/ Extract the first element of a ByteString, which must be non-empty.
-- An exception will be thrown in the case of an empty ByteString.
{-@ head :: ByteStringNE -> Word8 @-}
head :: ByteString -> Word8
head (PS x s l)
    | l <= 0    = errorEmptyList "head"
    | otherwise = inlinePerformIO $ withForeignPtr x $ \p -> peekByteOff p s
{-# INLINE head #-}

-- | /O(1)/ Extract the elements after the head of a ByteString, which must be non-empty.
-- An exception will be thrown in the case of an empty ByteString.
{-@ tail :: b:ByteStringNE -> {v:ByteString | (bLength v) = (bLength b) - 1} @-}
tail :: ByteString -> ByteString
tail (PS p s l)
    | l <= 0    = errorEmptyList "tail"
    | otherwise = PS p (s+1) (l-1)
{-# INLINE tail #-}

-- | /O(1)/ Extract the head and tail of a ByteString, returning Nothing
-- if it is empty.
{-@ uncons :: b:ByteString -> Maybe (Word8, {v:ByteString | (bLength v) = (bLength b) - 1}) @-}
uncons :: ByteString -> Maybe (Word8, ByteString)
uncons (PS x s l)
    | l <= 0    = Nothing
    | otherwise = Just (inlinePerformIO $ withForeignPtr x
                                        $ \p -> peekByteOff p s,
                        PS x (s+1) (l-1))
{-# INLINE uncons #-}

-- | /O(1)/ Extract the last element of a ByteString, which must be finite and non-empty.
-- An exception will be thrown in the case of an empty ByteString.
{-@ last :: ByteStringNE -> Word8 @-}
last :: ByteString -> Word8
last ps@(PS x s l)
    | null ps   = errorEmptyList "last"
    | otherwise = inlinePerformIO $ withForeignPtr x $ \p -> peekByteOff p (s+l-1)
{-# INLINE last #-}

-- | /O(1)/ Return all the elements of a 'ByteString' except the last one.
-- An exception will be thrown in the case of an empty ByteString.
{-@ init :: b:ByteStringNE -> {v:ByteString | (bLength v) = (bLength b) - 1} @-}
init :: ByteString -> ByteString
init ps@(PS p s l)
    | null ps   = errorEmptyList "init"
    | otherwise = PS p s (l-1)
{-# INLINE init #-}

-- | /O(n)/ Append two ByteStrings
{-@ append :: b1:ByteString -> b2:ByteString 
           -> {v:ByteString | (bLength v) = (bLength b1) + (bLength b2)} 
  @-}
append :: ByteString -> ByteString -> ByteString
append xs ys | null xs   = ys
             | null ys   = xs
             | otherwise = concat [xs,ys]
{-# INLINE append #-}

-- ---------------------------------------------------------------------
-- Transformations

-- | /O(n)/ 'map' @f xs@ is the ByteString obtained by applying @f@ to each
-- element of @xs@. This function is subject to array fusion.
{-@ map :: (Word8 -> Word8) -> b:ByteString -> (ByteStringSZ b) @-}
map :: (Word8 -> Word8) -> ByteString -> ByteString
map f (PS fp s len) = inlinePerformIO $ withForeignPtr fp $ \a ->
    create len $ map_ len 0 (a `plusPtr` s)
  where
    map_ :: Int -> Int -> Ptr Word8 -> Ptr Word8 -> IO ()
    STRICT4(map_)
  {- LIQUID WITNESS -}
    map_ (d :: Int) n p1 p2
       | n >= len = return ()
       | otherwise = do
            x <- peekByteOff p1 n
            pokeByteOff p2 n (f x)
            map_ (d-1) (n+1) p1 p2
{-# INLINE map #-}

-- | /O(n)/ 'reverse' @xs@ efficiently returns the elements of @xs@ in reverse order.

{-@ reverse :: b:ByteString -> (ByteStringSZ b) @-}
reverse :: ByteString -> ByteString
reverse (PS x s l) = unsafeCreate l $ \p -> withForeignPtr x $ \f ->
        c_reverse p (f `plusPtr` s) (fromIntegral l)

-- | /O(n)/ The 'intersperse' function takes a 'Word8' and a
-- 'ByteString' and \`intersperses\' that byte between the elements of
-- the 'ByteString'.  It is analogous to the intersperse function on
-- Lists.
{-@ intersperse :: Word8 -> b:ByteString
                -> {v:ByteString |
                     (((bLength b) > 0) ? ((bLength v) = (2 * (bLength b)) - 1)
                                          : ((bLength v) = 0)) }
  @-}
intersperse :: Word8 -> ByteString -> ByteString
intersperse c ps@(PS x s l)
    | length ps < 2  = ps
    | otherwise      = unsafeCreate ({- 2*l -} (l + l) - 1) $ \p -> withForeignPtr x $ \f ->
        c_intersperse p (f `plusPtr` s) (fromIntegral l) c

{-
intersperse c = pack . List.intersperse c . unpack
-}

-- | The 'transpose' function transposes the rows and columns of its
-- 'ByteString' argument.
transpose :: [ByteString] -> [ByteString]
transpose ps = P.map pack (List.transpose (P.map unpack ps))

-- LIQUID TODO
-- transpose :: bs:[ByteString] -> {v:[ByteString] | (bLengths v) = (bLengths bs)}
-- transpose :: xs:[[a]] -> {v:[[a]] | (lens v) = (lens xs)}
-- transpose ps = [pack p | p <- List.transpose [unpack p | p <- ps] ]


-- ---------------------------------------------------------------------
-- Reducing 'ByteString's

-- | 'foldl', applied to a binary operator, a starting value (typically
-- the left-identity of the operator), and a ByteString, reduces the
-- ByteString using the binary operator, from left to right.
-- This function is subject to array fusion.
{-@ foldl :: (a -> Word8 -> a) -> a -> ByteString -> a @-}
foldl :: (a -> Word8 -> a) -> a -> ByteString -> a
foldl f v (PS x s l) = inlinePerformIO $ withForeignPtr x $ \ptr ->
        go v (ptr `plusPtr` s) (ptr `plusPtr` (s+l)) (ptrLen (ptr `plusPtr` s))
    where
        STRICT4(go)
  {- LIQUID WITNESS -}
        go z p q (d::Int)
                  | p == q    = return z
                  | otherwise = do let p' = liquid_thm_ptr_cmp p q 
                                   c <- peek p'
                                   go (f z c) (p' `plusPtr` 1) q (d-1)
{-# INLINE foldl #-}


-- LIQUID: This will go away when we properly embed Ptr a as int -- only in
-- fixpoint to avoid the Sort mismatch hassles. 
{-@ liquid_thm_ptr_cmp :: p:PtrV a 
                       -> q:{v:(PtrV a) | ((plen v) <= (plen p) && v != p && (pbase v) = (pbase p))} 
                       -> {v: (PtrV a)  | ((v = p) && ((plen q) < (plen p))) } 
  @-}
liquid_thm_ptr_cmp :: Ptr a -> Ptr a -> Ptr a
liquid_thm_ptr_cmp p q = undefined -- p -- LIQUID : make this undefined to suppress WARNING


-- | 'foldl\'' is like 'foldl', but strict in the accumulator.
-- Though actually foldl is also strict in the accumulator.
{-@ foldl' :: (a -> Word8 -> a) -> a -> ByteString -> a @-}
foldl' :: (a -> Word8 -> a) -> a -> ByteString -> a
foldl' = foldl
{-# INLINE foldl' #-}

-- | 'foldr', applied to a binary operator, a starting value
-- (typically the right-identity of the operator), and a ByteString,
-- reduces the ByteString using the binary operator, from right to left.

-- foldr/foldr' TERMINATION
{-@ qualif PtrDiff(v:int, p:Ptr a, q:Ptr a): v >= (plen p) - (plen q) @-}

foldr :: (Word8 -> a -> a) -> a -> ByteString -> a
foldr k v (PS x s l) = inlinePerformIO $ withForeignPtr x $ \ptr ->
        go v (ptr `plusPtr` (s+l-1)) (ptr `plusPtr` (s-1)) l
    where
        STRICT4(go)
  {- LIQUID WITNESS -}
        go z p q (d::Int)
                 | p == q    = return z
                 | otherwise = do let p' = liquid_thm_ptr_cmp' p q 
                                  c  <- peek p'
                                  let n  = 0 - 1  
                                  go (c `k` z) (p' `plusPtr` n) q (d-1) -- tail recursive
        -- LIQUID go z p q | p == q    = return z
        -- LIQUID          | otherwise = do c  <- peek p
        -- LIQUID                           go (c `k` z) (p `plusPtr` (-1)) q -- tail recursive
{-# INLINE foldr #-}


{-@ liquid_thm_ptr_cmp' :: p:PtrV a 
                        -> q:{v:(PtrV a) | ((plen v) >= (plen p) && v != p && (pbase v) = (pbase p))} 
                        -> {v: (PtrV a)  | ((v = p) && ((plen v) > 0) && ((plen q) > (plen p))) } 
  @-}
liquid_thm_ptr_cmp' :: Ptr a -> Ptr a -> Ptr a
liquid_thm_ptr_cmp' p q = undefined 

-- | 'foldr\'' is like 'foldr', but strict in the accumulator.
foldr' :: (Word8 -> a -> a) -> a -> ByteString -> a
foldr' k v (PS x s l) = inlinePerformIO $ withForeignPtr x $ \ptr ->
        go v (ptr `plusPtr` (s+l-1)) (ptr `plusPtr` (s-1)) l
    where
        STRICT4(go)
  {- LIQUID WITNESS -}
        go z p q (d::Int)
                 | p == q    = return z
                 | otherwise = do let p' = liquid_thm_ptr_cmp' p q 
                                  c  <- peek p'
                                  let n  = 0 - 1  
                                  go (c `k` z) (p' `plusPtr` n) q (d-1) -- tail recursive
        -- LIQUID go z p q | p == q    = return z
        -- LIQUID          | otherwise = do c  <- peek p
        -- LIQUID                           go (c `k` z) (p `plusPtr` (-1)) q -- tail recursive
{-# INLINE foldr' #-}

-- | 'foldl1' is a variant of 'foldl' that has no starting value
-- argument, and thus must be applied to non-empty 'ByteStrings'.
-- This function is subject to array fusion. 
-- An exception will be thrown in the case of an empty ByteString.
{-@ foldl1 :: (Word8 -> Word8 -> Word8) -> ByteStringNE -> Word8 @-}
foldl1 :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldl1 f ps
    | null ps   = errorEmptyList "foldl1"
    | otherwise = foldl f (unsafeHead ps) (unsafeTail ps)
{-# INLINE foldl1 #-}

-- | 'foldl1\'' is like 'foldl1', but strict in the accumulator.
-- An exception will be thrown in the case of an empty ByteString.
{-@ foldl1' :: (Word8 -> Word8 -> Word8) -> ByteStringNE -> Word8 @-}
foldl1' :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldl1' f ps
    | null ps   = errorEmptyList "foldl1'"
    | otherwise = foldl' f (unsafeHead ps) (unsafeTail ps)
{-# INLINE foldl1' #-}

-- | 'foldr1' is a variant of 'foldr' that has no starting value argument,
-- and thus must be applied to non-empty 'ByteString's
-- An exception will be thrown in the case of an empty ByteString.

{-@ foldr1 :: (Word8 -> Word8 -> Word8) -> ByteStringNE -> Word8 @-}
foldr1 :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldr1 f ps
    | null ps        = errorEmptyList "foldr1"
    | otherwise      = foldr f (last ps) (init ps)
{-# INLINE foldr1 #-}

-- | 'foldr1\'' is a variant of 'foldr1', but is strict in the
-- accumulator.
{-@ foldr1' :: (Word8 -> Word8 -> Word8) -> ByteStringNE -> Word8 @-}
foldr1' :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldr1' f ps
    | null ps        = errorEmptyList "foldr1"
    | otherwise      = foldr' f (last ps) (init ps)
{-# INLINE foldr1' #-}

-- ---------------------------------------------------------------------
-- Special folds

-- | /O(n)/ Concatenate a list of ByteStrings.
{-@ concat :: bs:[ByteString] -> {v:ByteString | (bLength v) = (bLengths bs)} @-}
concat :: [ByteString] -> ByteString
concat []     = empty
concat [ps]   = ps
concat xs     = unsafeCreate len $ \ptr -> go xs ptr
  where len = {- LIQUID P.sum . P.map length $ -} lengths xs
        STRICT2(go)
        go []            _   = return ()
        go (PS p s l:ps) ptr = do
                -- LIQUID: could instead use  (also works)
                -- LIQUID {- invariant {v: [ByteString] | 0 <= (bLengths v)} -}
                let p'  = liquidAssert (lengths ps >= 0) p
                withForeignPtr p' $ \fp -> memcpy ptr (fp `plusPtr` s) (fromIntegral l)
                go ps (ptr `plusPtr` l)

-- | Map a function over a 'ByteString' and concatenate the results
concatMap :: (Word8 -> ByteString) -> ByteString -> ByteString
concatMap f = concat . foldr ((:) . f) []

-- foldr (append . f) empty

-- | /O(n)/ Applied to a predicate and a ByteString, 'any' determines if
-- any element of the 'ByteString' satisfies the predicate.
any :: (Word8 -> Bool) -> ByteString -> Bool
any _ (PS _ _ 0) = False
any f (PS x s l) = inlinePerformIO $ withForeignPtr x $ \ptr ->
        go (ptr `plusPtr` s) (ptr `plusPtr` (s+l)) (ptrLen (ptr `plusPtr` s)) 
    where
        STRICT3(go)
  {- LIQUID WITNESS -}
        go p q (d::Int) | p == q    = return False
                        | otherwise = do let p' = liquid_thm_ptr_cmp p q     -- LIQUID
                                         c <- peek p'
                                         if f c then return True
                                                else go (p' `plusPtr` 1) q (d-1)
{-# INLINE any #-}

-- todo fuse

-- | /O(n)/ Applied to a predicate and a 'ByteString', 'all' determines
-- if all elements of the 'ByteString' satisfy the predicate.
all :: (Word8 -> Bool) -> ByteString -> Bool
all _ (PS _ _ 0) = True
all f (PS x s l) = inlinePerformIO $ withForeignPtr x $ \ptr ->
        go (ptr `plusPtr` s) (ptr `plusPtr` (s+l)) (ptrLen (ptr `plusPtr` s))
    where
        STRICT3(go)
  {- LIQUID WITNESS -}
        go p q (d::Int)
               | p == q     = return True  -- end of list
               | otherwise  = do let p' = liquid_thm_ptr_cmp p q     -- LIQUID
                                 c <- peek p'
                                 if f c
                                    then go (p' `plusPtr` 1) q (d-1)
                                    else return False
{-# INLINE all #-}

------------------------------------------------------------------------

-- | /O(n)/ 'maximum' returns the maximum value from a 'ByteString'
-- This function will fuse.
-- An exception will be thrown in the case of an empty ByteString.
{-@ maximum :: ByteStringNE -> Word8 @-}
maximum :: ByteString -> Word8
maximum xs@(PS x s l)
    | null xs   = errorEmptyList "maximum"
    | otherwise = inlinePerformIO $ withForeignPtr x $ \p ->
                      c_maximum (p `plusPtr` s) (fromIntegral l)
{-# INLINE maximum #-}

-- | /O(n)/ 'minimum' returns the minimum value from a 'ByteString'
-- This function will fuse.
-- An exception will be thrown in the case of an empty ByteString.
{-@ minimum :: ByteStringNE -> Word8 @-}
minimum :: ByteString -> Word8
minimum xs@(PS x s l)
    | null xs   = errorEmptyList "minimum"
    | otherwise = inlinePerformIO $ withForeignPtr x $ \p ->
                      c_minimum (p `plusPtr` s) (fromIntegral l)
{-# INLINE minimum #-}

------------------------------------------------------------------------

-- | The 'mapAccumL' function behaves like a combination of 'map' and
-- 'foldl'; it applies a function to each element of a ByteString,
-- passing an accumulating parameter from left to right, and returning a
-- final value of this accumulator together with the new list.

{-@ mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> b:ByteString -> (acc, ByteStringSZ b) @-}
mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
#if !defined(LOOPU_FUSION)
mapAccumL f z b = unSP $ loopUp (mapAccumEFL f) z b
#else
mapAccumL f z b = unSP $ loopU (mapAccumEFL f) z b
#endif
{-# INLINE mapAccumL #-}

-- | The 'mapAccumR' function behaves like a combination of 'map' and
-- 'foldr'; it applies a function to each element of a ByteString,
-- passing an accumulating parameter from right to left, and returning a
-- final value of this accumulator together with the new ByteString.

{-@ mapAccumR :: (acc -> Word8 -> (acc, Word8)) -> acc -> b:ByteString -> (acc, ByteStringSZ b) @-}
mapAccumR :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumR f z b = unSP $ loopDown (mapAccumEFL f) z b
{-# INLINE mapAccumR #-}

-- | /O(n)/ map Word8 functions, provided with the index at each position
{-@ mapIndexed :: (Int -> Word8 -> Word8) -> b:ByteString -> ByteStringSZ b @-}
mapIndexed :: (Int -> Word8 -> Word8) -> ByteString -> ByteString
mapIndexed f b = loopArr $ loopUp (mapIndexEFL f) 0 b
{-# INLINE mapIndexed #-}

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

-- LIQUID TODO
{-@ scanl :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString  @-}
{- scanl :: (Word8 -> Word8 -> Word8) -> Word8 -> b:ByteString -> {v:ByteString | (bLength v) = 1 + (bLength b)}  @-}
scanl :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
#if !defined(LOOPU_FUSION)
scanl f z ps = loopArr . loopUp (scanEFL f) z $ (ps `snoc` 0)
#else
scanl f z ps = loopArr . loopU (scanEFL f) z $ (ps `snoc` 0)
#endif

    -- n.b. haskell's List scan returns a list one bigger than the
    -- input, so we need to snoc here to get some extra space, however,
    -- it breaks map/up fusion (i.e. scanl . map no longer fuses)
{-# INLINE scanl #-}

-- | 'scanl1' is a variant of 'scanl' that has no starting value argument.
-- This function will fuse.
--
-- > scanl1 f [x1, x2, ...] == [x1, x1 `f` x2, ...]
{- scanl1 :: (Word8 -> Word8 -> Word8) -> b:ByteStringNE -> {v:ByteStringNE | (bLength v) = 1 + (bLength b)} -}

-- LIQUID TODO
{-@ scanl1 :: (Word8 -> Word8 -> Word8) -> ByteStringNE -> ByteString @-}
scanl1 :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
scanl1 f ps
    | null ps   = empty
    | otherwise = scanl f (unsafeHead ps) (unsafeTail ps)
{-# INLINE scanl1 #-}

-- | scanr is the right-to-left dual of scanl.
-- LIQUID TODO
{-@ scanr :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString @-}
{- scanr :: (Word8 -> Word8 -> Word8) -> Word8 -> b:ByteString -> {v:ByteStringNE | (bLength v) = 1 + (bLength b)}  @-}
scanr :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
scanr f z ps = loopArr . loopDown (scanEFL (flip f)) z $ (0 `cons` ps) -- extra space
{-# INLINE scanr #-}

-- | 'scanr1' is a variant of 'scanr' that has no starting value argument.
-- LIQUID TODO
{-@ scanr1 :: (Word8 -> Word8 -> Word8) -> ByteStringNE -> ByteString @-}
{- scanr1 :: (Word8 -> Word8 -> Word8) -> b:ByteStringNE -> {v:ByteStringNE | (bLength v) = 1 + (bLength b)}  @-}
scanr1 :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
scanr1 f ps
    | null ps   = empty
    | otherwise = scanr f (last ps) (init ps) -- todo, unsafe versions
{-# INLINE scanr1 #-}

-- ---------------------------------------------------------------------
-- Unfolds and replicates

-- | /O(n)/ 'replicate' @n x@ is a ByteString of length @n@ with @x@
-- the value of every element. The following holds:
--
-- > replicate w c = unfoldr w (\u -> Just (u,u)) c
--
-- This implemenation uses @memset(3)@
{- LIQUID this is SIMPLER ... : replicate :: n:Nat -> Word8 -> (ByteStringN n) @-}
{-@ replicate :: n:Nat -> Word8 -> {v:ByteString | (bLength v) = (if n > 0 then n else 0)} @-}
replicate :: Int -> Word8 -> ByteString
replicate w c
    | w <= 0    = empty
    | otherwise = unsafeCreate w $ \ptr ->
                      memset ptr c (fromIntegral w) >> return ()

-- | /O(n)/, where /n/ is the length of the result.  The 'unfoldr' 
-- function is analogous to the List \'unfoldr\'.  'unfoldr' builds a 
-- ByteString from a seed value.  The function takes the element and 
-- returns 'Nothing' if it is done producing the ByteString or returns 
-- 'Just' @(a,b)@, in which case, @a@ is the next byte in the string, 
-- and @b@ is the seed value for further production.
--
-- Examples:
--
-- >    unfoldr (\x -> if x <= 5 then Just (x, x + 1) else Nothing) 0
-- > == pack [0, 1, 2, 3, 4, 5]

{-@ unfoldr :: (a -> Maybe (Word8, a)) -> a -> ByteString @-}
{-@ Strict Data.ByteString.unfoldr @-}
unfoldr :: (a -> Maybe (Word8, a)) -> a -> ByteString
unfoldr f = concat . unfoldChunk 32 64
  where unfoldChunk n n' x =
          case unfoldrN n f x of
            (s, Nothing) -> s : []
            (s, Just x') -> s : unfoldChunk n' (n+n') x'
{-# INLINE unfoldr #-}

-- | /O(n)/ Like 'unfoldr', 'unfoldrN' builds a ByteString from a seed
-- value.  However, the length of the result is limited by the first
-- argument to 'unfoldrN'.  This function is more efficient than 'unfoldr'
-- when the maximum length of the result is known.
--
-- The following equation relates 'unfoldrN' and 'unfoldr':
--
-- > unfoldrN n f s == take n (unfoldr f s)
--
{-@ unfoldrN :: i:Nat -> (a -> Maybe (Word8, a)) -> a -> ({v:ByteString | (bLength v) <= i}, Maybe a)<{\b m -> ((isJust m) => ((bLength b) = i))}> @-}
unfoldrN :: Int -> (a -> Maybe (Word8, a)) -> a -> (ByteString, Maybe a)
unfoldrN i f x0
    | i < 0     = (empty, Just x0)
    | otherwise = unsafePerformIO $ createAndTrimMEQ i $ \p -> go_unfoldrN i p x0 0
  where STRICT4(go)
  {- LIQUID WITNESS -}
        go_unfoldrN (d::Int) p x n =
          case f x of
            Nothing      -> return (0 :: Int {- LIQUID -}, n, Nothing)
            Just (w,x')
             | n == i    -> return (0, n, Just x)
             | otherwise -> do poke p w
                               go_unfoldrN (d-1) (p `plusPtr` 1) x' (n+1)
{-# INLINE unfoldrN #-}

{-@ unfoldqual :: l:Nat -> {v:(Nat, Nat, Maybe a) | (((tsnd v) <= (l-(tfst v)))
                                  && ((isJust (ttrd v)) => ((tsnd v)=l)))}  @-}
unfoldqual :: Int -> (Int, Int, Maybe a)
unfoldqual = undefined

-- ---------------------------------------------------------------------
-- Substrings

-- | /O(1)/ 'take' @n@, applied to a ByteString @xs@, returns the prefix
-- of @xs@ of length @n@, or @xs@ itself if @n > 'length' xs@.

{-@ take :: n:Nat -> b:ByteString -> {v:ByteString | (bLength v) = (if (n <= (bLength b)) then n else (bLength b))} @-}
take :: Int -> ByteString -> ByteString
take n ps@(PS x s l)
    | n <= 0    = empty
    | n >= l    = ps
    | otherwise = PS x s n
{-# INLINE take #-}

-- | /O(1)/ 'drop' @n xs@ returns the suffix of @xs@ after the first @n@
-- elements, or @[]@ if @n > 'length' xs@.

{-@ drop :: n:Nat -> b:ByteString -> {v:ByteString | (bLength v) =  (if (n <= (bLength b)) then (bLength b) - n else 0)} @-}
drop  :: Int -> ByteString -> ByteString
drop n ps@(PS x s l)
    | n <= 0    = ps
    | n >= l    = empty
    | otherwise = PS x (s+n) (l-n)
{-# INLINE drop #-}

-- | /O(1)/ 'splitAt' @n xs@ is equivalent to @('take' n xs, 'drop' n xs)@.

{-@ splitAt :: n:Int
            -> b:ByteString
            -> ({v:ByteString | (Min (bLength v) (bLength b)
                                     (if (n >= 0) then n else 0))}
               , ByteString)<{\x y -> (bLength y) = ((bLength b) - (bLength x))}>
  @-}
splitAt :: Int -> ByteString -> (ByteString, ByteString)
splitAt n ps@(PS x s l)
    | n <= 0    = (empty, ps)
    | n >= l    = (ps, empty)
    | otherwise = (PS x s n, PS x (s+n) (l-n))
{-# INLINE splitAt #-}

-- | 'takeWhile', applied to a predicate @p@ and a ByteString @xs@,
-- returns the longest prefix (possibly empty) of @xs@ of elements that
-- satisfy @p@.

{-@ takeWhile :: (Word8 -> Bool) -> b:ByteString -> (ByteStringLE b) @-}
takeWhile :: (Word8 -> Bool) -> ByteString -> ByteString
takeWhile f ps = unsafeTake (findIndexOrEnd (not . f) ps) ps
{-# INLINE takeWhile #-}

-- | 'dropWhile' @p xs@ returns the suffix remaining after 'takeWhile' @p xs@.
{-@ dropWhile :: (Word8 -> Bool) -> b:ByteString -> (ByteStringLE b) @-}
dropWhile :: (Word8 -> Bool) -> ByteString -> ByteString
dropWhile f ps = unsafeDrop (findIndexOrEnd (not . f) ps) ps
{-# INLINE dropWhile #-}

-- instead of findIndexOrEnd, we could use memchr here.

-- | 'break' @p@ is equivalent to @'span' ('not' . p)@.
{-@ break :: (Word8 -> Bool) -> b:ByteString -> (ByteStringPair b) @-}
break :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
break p ps = case findIndexOrEnd p ps of n -> (unsafeTake n ps, unsafeDrop n ps)
#if __GLASGOW_HASKELL__ 
{-# INLINE [1] break #-}

{-# RULES
"FPS specialise break (x==)" forall x.
    break ((==) x) = breakByte x
"FPS specialise break (==x)" forall x.
    break (==x) = breakByte x
  #-}
#endif

-- | 'breakByte' breaks its ByteString argument at the first occurence
-- of the specified byte. It is more efficient than 'break' as it is
-- implemented with @memchr(3)@. I.e.
-- 
-- > break (=='c') "abcd" == breakByte 'c' "abcd"
--

{-@ breakByte :: Word8 -> b:ByteString -> (ByteStringPair b) @-}
breakByte :: Word8 -> ByteString -> (ByteString, ByteString)
breakByte c p = case elemIndex c p of
    Nothing -> (p,empty)
    Just n  -> (unsafeTake n p, unsafeDrop n p)
{-# INLINE breakByte #-}

-- | 'breakEnd' behaves like 'break' but from the end of the 'ByteString'
-- 
-- breakEnd p == spanEnd (not.p)

{-@ breakEnd :: (Word8 -> Bool) -> b:ByteString -> (ByteStringPair b) @-}
breakEnd :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
breakEnd  p ps = splitAt (findFromEndUntil p ps) ps

-- | 'span' @p xs@ breaks the ByteString into two segments. It is
-- equivalent to @('takeWhile' p xs, 'dropWhile' p xs)@
{-@ span :: (Word8 -> Bool) -> b:ByteString -> (ByteStringPair b) @-}
span :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
span p ps = break (not . p) ps
#if __GLASGOW_HASKELL__
{-# INLINE [1] span #-}
#endif

-- | 'spanByte' breaks its ByteString argument at the first
-- occurence of a byte other than its argument. It is more efficient
-- than 'span (==)'
--
-- > span  (=='c') "abcd" == spanByte 'c' "abcd"
--
{-@ spanByte :: Word8 -> b:ByteString -> (ByteStringPair b) @-}
spanByte :: Word8 -> ByteString -> (ByteString, ByteString)
spanByte c ps@(PS x s l) = inlinePerformIO $ withForeignPtr x $ \p ->
    go l (p `plusPtr` s) 0
  where
    STRICT3(go)
  {- LIQUID WITNESS -}
    go (d::Int) p i | i >= l    = return (ps, empty)
                    | otherwise = do c' <- peekByteOff p i
                                     if c /= c'
                                       then return (unsafeTake i ps, unsafeDrop i ps)
                                       else go (d-1) p (i+1)
{-# INLINE spanByte #-}

{-# RULES
"FPS specialise span (x==)" forall x.
    span ((==) x) = spanByte x
"FPS specialise span (==x)" forall x.
    span (==x) = spanByte x
  #-}

-- | 'spanEnd' behaves like 'span' but from the end of the 'ByteString'.
-- We have
--
-- > spanEnd (not.isSpace) "x y z" == ("x y ","z")
--
-- and
--
-- > spanEnd (not . isSpace) ps
-- >    == 
-- > let (x,y) = span (not.isSpace) (reverse ps) in (reverse y, reverse x) 
--
{-@ spanEnd :: (Word8 -> Bool) -> b:ByteString -> (ByteStringPair b) @-}
spanEnd :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
spanEnd  p ps = splitAt (findFromEndUntil (not.p) ps) ps


-- | /O(n)/ intercalateWithByte. An efficient way to join to two ByteStrings
-- with a char. Around 4 times faster than the generalised join.
--

{-@ intercalateWithByte :: Word8 -> f:ByteString -> g:ByteString -> {v:ByteString | (bLength v) = (bLength f) + (bLength g) + 1} @-}
intercalateWithByte :: Word8 -> ByteString -> ByteString -> ByteString
intercalateWithByte c f@(PS ffp s l) g@(PS fgp t m) = unsafeCreate len $ \ptr ->
    withForeignPtr ffp $ \fp ->
    withForeignPtr fgp $ \gp -> do
        memcpy ptr (fp `plusPtr` s) (fromIntegral l)
        poke (ptr `plusPtr` l) c
        memcpy (ptr `plusPtr` (l + 1)) (gp `plusPtr` t) (fromIntegral m)
    where
      len = length f + length g + 1
{-# INLINE intercalateWithByte #-}



-- ---------------------------------------------------------------------
-- ** Ordered 'ByteString's

-- | /O(n)/ Sort a ByteString efficiently, using counting sort.
-- LIQUID FAIL: requires invariant that SUM of cells in intermediate array
-- equals total len of outer array. WHOA. Due to Ptr issue, this gets
-- "proved" safe. Oh boy. Still, can prove that output size = input size.

--LIQUID sortCanary :: Int -> Int
--LIQUID sortCanary x = liquidAssert (0 == 1) x

sort :: ByteString -> ByteString
sort (PS input s l) = unsafeCreate l $ \p -> allocaArray 256 $ \arr -> do

    memset (castPtr arr) 0 (256 * fromIntegral (sizeOf (undefined :: CSize)))
    withForeignPtr input (\x -> countOccurrences arr (x `plusPtr` s) l)

    let STRICT2(go)
        go 256 _   = return ()
        go i   ptr = do n <- peekElemOff arr i
                        when (n /= 0) $ memset ptr (fromIntegral i) n >> return ()
                        go (i + 1) (ptr `plusPtr` (fromIntegral n))
    go 0 p
  where
    -- | Count the number of occurrences of each byte.
    -- Used by 'sort'
    --
    countOccurrences :: Ptr CSize -> Ptr Word8 -> Int -> IO ()
    STRICT3(countOccurrences)
    countOccurrences counts str len = go 0
     where
        STRICT1(go)
        go i | i == len    = return ()
             | otherwise = do k <- fromIntegral `fmap` peekElemOff str i
                              x <- peekElemOff counts k
                              pokeElemOff counts k (x + 1)
                              go (i + 1)

-- ---------------------------------------------------------------------
-- Internal utilities

-- | 'findIndexOrEnd' is a variant of findIndex, that returns the length
-- of the string if no element is found, rather than Nothing.
{-@ findIndexOrEnd :: (Word8 -> Bool) -> b:ByteString -> {v:Nat | v <= (bLength b) } @-}
findIndexOrEnd :: (Word8 -> Bool) -> ByteString -> Int
findIndexOrEnd k (PS x s l) = inlinePerformIO $ withForeignPtr x $ \f -> go l (f `plusPtr` s) 0
  where
    STRICT3(go)
  {- LIQUID WITNESS -}
    go (d::Int) ptr n | n >= l    = return l
                      | otherwise = do w <- peek ptr
                                       if k w
                                         then return n
                                         else go (d-1) (ptr `plusPtr` 1) (n+1)
{-# INLINE findIndexOrEnd #-}

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

-- Find from the end of the string using predicate
{-@ findFromEndUntil :: (Word8 -> Bool) -> b:ByteString -> {v:Nat | v <= (bLength b)} @-}
findFromEndUntil :: (Word8 -> Bool) -> ByteString -> Int
STRICT2(findFromEndUntil)
findFromEndUntil f ps@(PS x s l) =
    if null ps then 0
    else if f (last ps) then l
         else findFromEndUntil f (PS x s (l-1))

{-@ split :: Word8 -> b:ByteStringNE -> (ByteStringSplit b)  @-}
split :: Word8 -> ByteString -> [ByteString]
split _ (PS _ _ 0) = []
split w (PS x s l) = inlinePerformIO $ withForeignPtr x $ \p -> do
    let ptr = p `plusPtr` s

        STRICT2(loop)
  {- LIQUID WITNESS -}
        loop (d::Int) n =
            -- LIQUID: else lose `plen` info due to subsequent @ Word8 application
            let ptrn = (ptr `plusPtr` n) :: Ptr Word8 
                q = inlinePerformIO $ memchr ptrn {- (ptr `plusPtr` n) -}
                                           w (fromIntegral (l-n))
            in if isNullPtr q {- LIQUID q == nullPtr -}
                then [PS x (s+n) (l-n)]
                else let i = q `minusPtr` ptr in PS x (s+n) (i-n) : loop (l - (i+1)) (i+1)

    return (loop l 0)
{-# INLINE split #-}


{-@ splitWith :: (Word8 -> Bool) -> b:ByteStringNE -> (ByteStringSplit b) @-}
splitWith :: (Word8 -> Bool) -> ByteString -> [ByteString]

splitWith _pred (PS _  _   0) = []
splitWith pred_ (PS fp off len) = splitWith0 pred# off len fp 1
  where pred# c# = pred_ (W8# c#)
        -- LIQUID MUTUAL-RECURSION-TERMINATION
        {-@ Decrease splitWith0 3 5 @-}
        --LIQUID STRICT5(splitWith0)
  {- LIQUID WITNESS -}
        splitWith0 pred' off' len' fp' (x::Int) = withPtr fp $ \p ->
            splitLoop pred' p 0 off' len' fp' len' 0

        {-@ Decrease splitLoop 7 8 @-}
        splitLoop :: (Word# -> Bool)
                  -> Ptr Word8
                  -> Int -> Int -> Int
                  -> ForeignPtr Word8 -> Int -> Int
                  -> IO [ByteString]

  {- LIQUID WITNESS -}
        splitLoop pred' p idx' off' len' fp' (d::Int) (x::Int)
            | pred' `seq` p `seq` idx' `seq` off' `seq` len' `seq` fp' `seq` False = undefined
            | idx' >= len'  = return [PS fp' off' idx']
            | otherwise = do
                w <- peekElemOff p (off'+idx')
                if pred' (case w of W8# w# -> w#)
                   then return (PS fp' off' idx' :
                              splitWith0 pred' (off'+idx'+1) (len'-idx'-1) fp' 1)
                   else splitLoop pred' p (idx'+1) off' len' fp' (d-1) 0
{-# INLINE splitWith #-}



{-@ group :: b:ByteString -> {v: [ByteStringNE] | (bLengths v) = (bLength b)} @-}
group :: ByteString -> [ByteString]
group xs
    | null xs   = []
    | otherwise = let y = unsafeHead xs
                      (ys, zs) = spanByte (unsafeHead xs) (unsafeTail xs)
                  in (y `cons` ys) : group zs
    -- LIQUID FIXME: a better spec for spanByte would say that if x
    -- occurs at the head of xs, then `spanByte x xs` will return a
    -- non-empty bytestring
    -- LIQUID where
    -- LIQUID     (ys, zs) = spanByte (unsafeHead xs) xs

{-@ groupBy :: (Word8 -> Word8 -> Bool) -> b:ByteString -> {v:[ByteStringNE] | (bLengths v) = (bLength b)} @-}
groupBy :: (Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]
groupBy k xs
    | null xs   = []
    | otherwise = let n = 1 + findIndexOrEnd (not . k (unsafeHead xs)) (unsafeTail xs) in
                  unsafeTake n xs : groupBy k (unsafeDrop n xs)
    -- LIQUID LAZY: where
    -- LIQUID LAZY:     n = 1 + findIndexOrEnd (not . k (unsafeHead xs)) (unsafeTail xs)


{-@ inits :: b:ByteString -> [{v1:ByteString | (bLength v1) <= (bLength b)}]<{\ix iy -> (bLength ix) < (bLength iy)}> @-}
inits :: ByteString -> [ByteString]
--LIQUID INLINE inits (PS x s l) = [PS x s n | n <- [0..l]]
inits (PS x s l) = PS x s 0 : go_inits 0 (rng 1 l)
    where
      {-@ Decrease go_inits 2 @-}
      go_inits _  []      = []
      go_inits n0 (n:ns)  = PS x s n : go_inits n ns

{-@ qualif RangeDecr(v:Int,x:Int, y:Int): v = 1 + x - y @-}
rng :: Int -> Int -> [Int]
rng lo hi            = go_rng (1 + hi - lo) lo
  where 
  {- LIQUID WITNESS -}
    go_rng (d::Int) i
         | i > hi    = []
         | otherwise = i : go_rng (d-1) (i+1)

-- LIQUID NOTES:
--   d - 1 = hi - i
--   d + i = hi + 1
--   0    <= hi - i


{-@ tails :: b:ByteString -> {v:[{v1:ByteString | (bLength v1) <= (bLength b)}] | (len v) = 1 + (bLength b)} @-}
tails :: ByteString -> [ByteString]
tails p | null p    = [empty]
        | otherwise = p : tails (unsafeTail p)

{-@ elemIndex :: Word8 -> b:ByteString -> Maybe {v:Nat | v < (bLength b)} @-}
elemIndex :: Word8 -> ByteString -> Maybe Int
elemIndex c (PS x s l) = inlinePerformIO $ withForeignPtr x $ \p -> do
    let p' = p `plusPtr` s
    q <- memchr p' c (fromIntegral l)
    return $! if isNullPtr q {- LIQUID: q == nullPtr -} then Nothing else Just $! q `minusPtr` p'
{-# INLINE elemIndex #-}


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
    go l (p `plusPtr` s) (l-1)
  where
    STRICT3(go)
  {- LIQUID WITNESS -}
    go (d::Int) p i    -- LIQUID TERMINATION
           | i < 0     = return Nothing
           | otherwise = do ch' <- peekByteOff p i
                            if ch == ch'
                                then return $ Just i
                                else go (d-1) p (i-1)

{-@ elemIndices :: Word8 -> b:ByteString -> [{v:Nat | v < (bLength b) }] @-}
elemIndices :: Word8 -> ByteString -> [Int]
elemIndices w (PS x s l) = inlinePerformIO $ withForeignPtr x $ \p -> do
    let ptr = p `plusPtr` s

        STRICT2(loop)
  {- LIQUID WITNESS -}
        loop (d::Int) n -- LIQUID TERMINATION
               = let pn = ((ptr `plusPtr` n) :: Ptr Word8)
                     q  = inlinePerformIO $ memchr pn
                                                 w (fromIntegral (l - n))
                 in if isNullPtr q {- == nullPtr -}
                        then []
                        else let i = q `minusPtr` ptr
                             in i : loop (l - (i+1)) (i+1)
    return $! loop l 0


{-@ count :: Word8 -> b:ByteString -> {v:Nat | v <= (bLength b) } @-}
count :: Word8 -> ByteString -> Int
count w (PS x s m) = inlinePerformIO $ withForeignPtr x $ \p ->
    fmap fromIntegral $ c_count (p `plusPtr` s) (fromIntegral m) w

{-@ findIndex :: (Word8 -> Bool) -> b:ByteString -> (Maybe {v:Nat | v < (bLength b)}) @-}
findIndex :: (Word8 -> Bool) -> ByteString -> Maybe Int
findIndex k (PS x s l) = inlinePerformIO $ withForeignPtr x $ \f -> go l (f `plusPtr` s) 0
  where
    STRICT3(go)
  {- LIQUID WITNESS -}
    go (d::Int) ptr n    -- LIQUID TERMINATION
             | n >= l    = return Nothing
             | otherwise = do w <- peek ptr
                              if k w
                                then return (Just n)
                                else go (d-1) (ptr `plusPtr` 1) (n+1)

-- also findSubstrings
{-@ qualif FindIndices(v:ByteString,
                       p:ByteString,
                       n:Int):
        (bLength v) = (bLength p) - n  @-}

{-@ findIndices :: (Word8 -> Bool) -> b:ByteString -> [{v:Nat | v < (bLength b)}] @-}
findIndices :: (Word8 -> Bool) -> ByteString -> [Int]
findIndices p ps = loopFindIndices 0 ps
   where
     STRICT2(loopFindIndices)
     {-@ Decrease loopFindIndices 2 @-}
  {- LIQUID WITNESS -}
     loopFindIndices (n :: Int) qs
        | null qs           = []
        | p (unsafeHead qs) = n : loopFindIndices (n+1) (unsafeTail qs)
        | otherwise         =     loopFindIndices (n+1) (unsafeTail qs)


elem :: Word8 -> ByteString -> Bool
elem c ps = case elemIndex c ps of Nothing -> False ; _ -> True
{-# INLINE elem #-}

notElem :: Word8 -> ByteString -> Bool
notElem c ps = not (elem c ps)
{-# INLINE notElem #-}

{-@ qualif FilterDecr(v:Ptr a, f:Ptr a, d:Int):
        (plen v) >= (plen f) - d @-}

{-@ qualif FilterLoop(v:Ptr a, f:Ptr a, t:Ptr a):
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
  {- LIQUID WITNESS -}
      go (d::Int) f' t end  -- LIQUID TERMINATION
                  | f' == end = return t
                  | otherwise = do
                        let f = liquid_thm_ptr_cmp f' end
                        w <- peek f
                        if k w
                          then poke t w >> go (d-1) (f `plusPtr` 1) (t `plusPtr` 1) end
                          else             go (d-1) (f `plusPtr` 1) t               end



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

-- | Alias of 'isSubstringOf'
isInfixOf :: ByteString -> ByteString -> Bool
isInfixOf = isSubstringOf


-- | Check whether one string is a substring of another. @isSubstringOf
-- p s@ is equivalent to @not (null (findSubstrings p s))@.
isSubstringOf :: ByteString -- ^ String to search for.
              -> ByteString -- ^ String to search in.
              -> Bool
isSubstringOf p s = not $ P.null $ findSubstrings p s

{-# DEPRECATED findSubstring "Do not use. The ByteString searching api is about to be replaced." #-}
-- | Get the first index of a substring in another string,
--   or 'Nothing' if the string is not found.
--   @findSubstring p s@ is equivalent to @listToMaybe (findSubstrings p s)@.

{-@ findSubstring :: pat:ByteString -> str:ByteString -> (Maybe {v:Nat | v <= (bLength str)}) @-}
findSubstring :: ByteString -- ^ String to search for.
              -> ByteString -- ^ String to seach in.
              -> Maybe Int
-- LIQUID ETA findSubstring = (listToMaybe .) . findSubstrings
findSubstring pat str = listToMaybe $ findSubstrings pat str

{-@ findSubstrings :: pat:ByteString -> str:ByteString -> [{v:Nat | v <= (bLength str)}] @-}
findSubstrings :: ByteString -- ^ String to search for.
               -> ByteString -- ^ String to seach in.
               -> [Int]

-- LIQUID LATEST 
findSubstrings pat str
    | null pat         = rng 0 (length str - 1) -- LIQUID COMPREHENSIONS [0 .. (length str - 1)]
    | otherwise        = searchFS 0 str
  where
    STRICT2(searchFS)
    {-@ Decrease searchFS 2 @-} 
  {- LIQUID WITNESS -}
    searchFS (n :: Int) s
        | null s             = []
        | pat `isPrefixOf` s = n : searchFS (n+1) (unsafeTail s)
        | otherwise          =     searchFS (n+1) (unsafeTail s)


{-@ breakSubstring :: ByteString -> b:ByteString -> (ByteStringPair b) @-}

breakSubstring :: ByteString -- ^ String to search for
               -> ByteString -- ^ String to search in
               -> (ByteString,ByteString) -- ^ Head and tail of string broken at substring

breakSubstring pat src = searchBS 0 src
  where
    STRICT2(searchBS)
    {-@ Decrease searchBS 2 @-}
    searchBS n s
        | null s             = (src, empty)      -- not found
        | pat `isPrefixOf` s = (take n src,s)
        | otherwise          = searchBS (n+1) (unsafeTail s)


{-@ useAsCString :: p:ByteString -> ({v:CString | (bLength p) + 1 = (plen v)} -> IO a) -> IO a @-}
useAsCString :: ByteString -> (CString -> IO a) -> IO a
useAsCString (PS fp o l) action = do
 allocaBytes (l+1) $ \buf ->
   withForeignPtr fp $ \p -> do
     memcpy buf (p `plusPtr` o) (fromIntegral l)
     pokeByteOff buf l (0::Word8)
     action (castPtr buf)

{-@ useAsCStringLen :: b:ByteString -> ({v:CStringLen | (cStringLen v) = (bLength b)} -> IO a) -> IO a @-}
useAsCStringLen :: ByteString -> (CStringLen -> IO a) -> IO a
useAsCStringLen p@(PS _ _ l) f = useAsCString p $ \cstr -> f (cstr, l)

{-@ packCString :: c:CString -> IO {v:ByteString | (bLength v) = (plen c)} @-}
packCString :: CString -> IO ByteString
packCString cstr = do
    len <- c_strlen cstr
    packCStringLen (cstr, fromIntegral len)


{-@ packCStringLen :: c:CStringLen -> (IO {v:ByteString | (bLength v) = (cStringLen c)}) @-}
packCStringLen :: CStringLen -> IO ByteString
packCStringLen (cstr, len) = create len $ \p ->
    memcpy p (castPtr cstr) (fromIntegral len)


{-@ copy :: b:ByteString -> (ByteStringSZ b) @-}
copy :: ByteString -> ByteString
copy (PS x s l) = unsafeCreate l $ \p -> withForeignPtr x $ \f ->
    memcpy p (f `plusPtr` s) (fromIntegral l)


{-@ predicate ZipLen V X Y = (len V) = (if (bLength X) <= (bLength Y) then (bLength X) else (bLength Y)) @-}
{-@ zip :: x:ByteString -> y:ByteString -> {v:[(Word8, Word8)] | (ZipLen v x y) } @-}
zip :: ByteString -> ByteString -> [(Word8,Word8)]
zip ps qs
    | null ps || null qs = []
    | otherwise = (unsafeHead ps, unsafeHead qs) : zip (unsafeTail ps) (unsafeTail qs)

{-@ zipWith :: (Word8 -> Word8 -> a) -> x:ByteString -> y:ByteString -> {v:[a] | (ZipLen v x y)} @-}
zipWith :: (Word8 -> Word8 -> a) -> ByteString -> ByteString -> [a]
zipWith f ps qs
    | null ps || null qs = []
    | otherwise = f (unsafeHead ps) (unsafeHead qs) : zipWith f (unsafeTail ps) (unsafeTail qs)


{-@ unzip :: z:[(Word8,Word8)] -> ({v:ByteString | (bLength v) = (len z)}, {v:ByteString | (bLength v) = (len z) }) @-}
unzip :: [(Word8,Word8)] -> (ByteString,ByteString)
unzip ls = (pack (P.map fst ls), pack (P.map snd ls))

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
  {- LIQUID WITNESS -}
    zipWith_ (d::Int) n p1 p2 r -- LIQUID TERMINATION
       | n >= len = return ()
       | otherwise = do
            x <- peekByteOff p1 n
            y <- peekByteOff p2 n
            pokeByteOff r n (f x y)
            zipWith_ (d-1) (n+1) p1 p2 r

    len = min l m


----- IO : trivial


getLine :: IO ByteString
getLine = hGetLine stdin


hGetLine h = wantReadableHandleLIQUID "Data.ByteString.hGetLine" h $ \ handle_ -> do
    case haBufferMode handle_ of
       NoBuffering -> error "no buffering"
       _other      -> hGetLineBuffered handle_

 where
    hGetLineBuffered handle_ = do
        let ref = haCharBuffer handle_
        buf <- readIORef ref
        hGetLineBufferedLoop handle_ ref buf 0 []

    hGetLineBufferedLoop handle_ ref
            buf@Buffer{ bufL=r, bufR=w, bufRaw=raw } len xss =
        len `seq` do
        off <- findEOL r w raw
        let new_len = len + off - r
        xs <- mkPS raw r off

      -- if eol == True, then off is the offset of the '\n'
      -- otherwise off == w and the buffer is now empty.
        if off /= w
            then do if (w == off + 1)
                            then writeIORef ref buf{ bufL=0, bufR=0 }
                            else writeIORef ref buf{ bufL = off + 1 }
                    mkBigPS new_len (xs:xss)
            else do
                 maybe_buf <- maybeFillReadBuffer ({- LIQUID COMPAT: haFD -} handle_) True ({- LIQUID COMPAT: haIsStream -} handle_)
                                    buf{ bufR=0, bufL=0 }
                 case maybe_buf of
                    -- Nothing indicates we caught an EOF, and we may have a
                    -- partial line to return.
                    Nothing -> do
                         writeIORef ref buf{ bufL=0, bufR=0 }
                         if new_len > 0
                            then mkBigPS new_len (xs:xss)
                            else error "LIQUIDCOMPAT" -- ioe_EOF
                    Just new_buf ->
                         hGetLineBufferedLoop handle_ ref new_buf new_len (xs:xss)

    -- find the end-of-line character, if there is one
    findEOL r w raw
        | r == w = return w
        | otherwise =  do
            (c,r') <- readCharFromBuffer raw r
            if c == '\n'
                then return r -- NB. not r': don't include the '\n'
                else findEOL r' w raw

    -- LIQUID COMPAT
    maybeFillReadBuffer fd is_line is_stream buf = return Nothing
    -- maybeFillReadBuffer fd is_line is_stream buf = catch
    --     (do buf' <- fillReadBuffer fd is_line is_stream buf
    --         return (Just buf'))
    --     (\e -> if isEOFError e then return Nothing else ioError e)

-- TODO, rewrite to use normal memcpy
mkPS :: RawBuffer Char -> Int -> Int -> IO ByteString
mkPS buf start end =
    let len = end - start
    in create len $ \p -> do
        memcpy_ptr_baoff p buf (fromIntegral start) ({- LIQUID fromIntegral-} intCSize len)
        return ()



mkBigPS :: Int -> [ByteString] -> IO ByteString
mkBigPS _ [ps] = return ps
mkBigPS _ pss = return $! concat (P.reverse pss)



-- | Outputs a 'ByteString' to the specified 'Handle'.
hPut :: Handle -> ByteString -> IO ()
hPut _ (PS _  _ 0) = return ()
hPut h (PS ps s l) = withForeignPtr ps $ \p-> hPutBuf h (p `plusPtr` s) l

-- | A synonym for @hPut@, for compatibility 
hPutStr :: Handle -> ByteString -> IO ()
hPutStr = hPut

-- | Write a ByteString to a handle, appending a newline byte
hPutStrLn :: Handle -> ByteString -> IO ()
hPutStrLn h ps
    | length ps < 1024 = hPut h (ps `snoc` 0x0a)
    | otherwise        = hPut h ps >> hPut h (singleton (0x0a)) -- don't copy

-- | Write a ByteString to stdout
putStr :: ByteString -> IO ()
putStr = hPut stdout

-- | Write a ByteString to stdout, appending a newline byte
putStrLn :: ByteString -> IO ()
putStrLn = hPutStrLn stdout

-- | Read a 'ByteString' directly from the specified 'Handle'.  This
-- is far more efficient than reading the characters into a 'String'
-- and then using 'pack'.

{-@ hGet :: Handle -> n:Nat -> IO {v:ByteString | (bLength v) <= n} @-}
hGet :: Handle -> Int -> IO ByteString
hGet _ 0 = return empty
hGet h i = createAndTrim i $ \p -> hGetBuf h p i

{-@ hGetNonBlocking :: Handle -> n:Nat -> IO {v:ByteString | (bLength v) <= n} @-}

hGetNonBlocking :: Handle -> Int -> IO ByteString
#if defined(__GLASGOW_HASKELL__)
hGetNonBlocking _ 0 = return empty
hGetNonBlocking h i = createAndTrim i $ \p -> hGetBufNonBlocking h p i
#else
hGetNonBlocking = hGet
#endif

{-@ assume Foreign.Marshal.Alloc.reallocBytes :: p:(Ptr a) -> n:Nat -> (IO (PtrN a n))  @-}
{-@ Lazy hGetContents @-}
hGetContents :: Handle -> IO ByteString
hGetContents h = do
    let start_size = 1024
    p <- mallocBytes start_size
    i <- hGetBuf h p start_size
    if i < start_size
        then do p' <- reallocBytes p i
                fp <- newForeignPtr finalizerFree p'
                return $! PS fp 0 i
        else go_hGetContents p start_size
    where
        -- LIQUID POTENTIALLY NON-TERMINATING!
        go_hGetContents p s = do
            let s' = s + s -- 2 * s -- LIQUID MULTIPLY
            p' <- reallocBytes p s'
            i  <- hGetBuf h (p' `plusPtr` s) s
            if i < s
                then do let i' = s + i
                        p'' <- reallocBytes p' i'
                        fp  <- newForeignPtr finalizerFree p''
                        return $! PS fp 0 i'
                else go_hGetContents p' s'



-- | getContents. Equivalent to hGetContents stdin
getContents :: IO ByteString
getContents = hGetContents stdin

-- | The interact function takes a function of type @ByteString -> ByteString@
-- as its argument. The entire input from the standard input device is passed
-- to this function as its argument, and the resulting string is output on the
-- standard output device. It's great for writing one line programs!
interact :: (ByteString -> ByteString) -> IO ()
interact transformer = putStr . transformer =<< getContents

-- | Read an entire file strictly into a 'ByteString'.  This is far more
-- efficient than reading the characters into a 'String' and then using
-- 'pack'.  It also may be more efficient than opening the file and
-- reading it using hGet. Files are read using 'binary mode' on Windows,
-- for 'text mode' use the Char8 version of this function.
readFile :: FilePath -> IO ByteString
readFile f = bracket (openBinaryFile f ReadMode) hClose
    (\h -> hFileSize h >>= hGet h . fromIntegral)

-- | Write a 'ByteString' to a file.
writeFile :: FilePath -> ByteString -> IO ()
writeFile f txt = bracket (openBinaryFile f WriteMode) hClose
    (\h -> hPut h txt)

-- | Append a 'ByteString' to a file.
appendFile :: FilePath -> ByteString -> IO ()
appendFile f txt = bracket (openBinaryFile f AppendMode) hClose
    (\h -> hPut h txt)

