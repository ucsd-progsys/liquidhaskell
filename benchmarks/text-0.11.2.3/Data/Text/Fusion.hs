{-# LANGUAGE BangPatterns, MagicHash #-}

-- |
-- Module      : Data.Text.Fusion
-- Copyright   : (c) Tom Harper 2008-2009,
--               (c) Bryan O'Sullivan 2009-2010,
--               (c) Duncan Coutts 2009
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com, rtomharper@googlemail.com,
--               duncan@haskell.org
-- Stability   : experimental
-- Portability : GHC
--
-- Text manipulation functions represented as fusible operations over
-- streams.
module Data.Text.Fusion
    (
    -- * Types
      Stream(..)
    , Step(..)

    -- * Creation and elimination
    , stream
    , unstream
    , reverseStream

    , length

    -- * Transformations
    , reverse

    -- * Construction
    -- ** Scans
    , reverseScanr

    -- ** Accumulating maps
    , mapAccumL

    -- ** Generation and unfolding
    , unfoldrN

    -- * Indexing
    , index
    , findIndex
    , countChar
    ) where

import Prelude (Bool(..), Char, Maybe(..), Monad(..), Int,
                Num(..), Ord(..), ($), (&&),
                fromIntegral, otherwise)
import Data.Bits ((.&.))
import Data.Text.Internal (Text(..))
import Data.Text.Private (runText)
import Data.Text.UnsafeChar (ord, unsafeChr, unsafeWrite)
import Data.Text.UnsafeShift (shiftL, shiftR)
import qualified Data.Text.Array as A
import qualified Data.Text.Fusion.Common as S
import Data.Text.Fusion.Internal
import Data.Text.Fusion.Size
import qualified Data.Text.Internal as I
import qualified Data.Text.Encoding.Utf16 as U16

--LIQUID
import GHC.ST (runST)
import Language.Haskell.Liquid.Prelude


default(Int)

{-@ qualif LTPlus(v:int, a:int, b:int) : v < (a + b) @-}
{-@ qualif LTEPlus(v:int, a:int, b:int) : (v + a) <= b @-}

{-@ qualif Ord(v:int, x:Char)
        : ((((ord x) <  65536) => (v = 0))
        && (((ord x) >= 65536) => (v = 1)))
  @-}
{-@ qualif Ord(v:int, i:int, x:Char)
        : ((((ord x) <  65536) => (v = i))
        && (((ord x) >= 65536) => (v = (i + 1))))
  @-}
{-@ qualif Ord(v:Char, i:int)
        : ((((ord x) <  65536) => (v >= 0))
        && (((ord x) >= 65536) => (v >= 1)))
  @-}

{-@ qualif MALenLE(v:int, a:A.MArray s): v <= (malen a) @-}
{-@ qualif ALenLE(v:int, a:A.Array): v <= (alen a) @-}

{-@ qualif Foo(v:a, a:A.MArray s):
        (snd v) <= (malen a)
  @-}
{-@ qualif Foo(v:a, a:A.Array):
        (snd v) <= (alen a)
  @-}

{-@ qualif Foo(v:int): v >= -1 @-}
{-@ qualif Foo(v:int): v >=  4 @-}

-- | /O(n)/ Convert a 'Text' into a 'Stream Char'.
stream :: Text -> Stream Char
stream (Text arr off len) = Stream next off (maxSize len)
    where
      !end = off+len
      next !i
          | i >= end  = Done
          | otherwise =
              let n  = A.unsafeIndexF arr off len i
              in if n >= 0xD800 && n <= 0xDBFF
                 then let n2 = A.unsafeIndex arr (i + 1)
                      in Yield (U16.chr2 n n2) (i + 2)
                 else Yield (unsafeChr n) (i + 1)
--LIQUID           | n >= 0xD800 && n <= 0xDBFF = Yield (U16.chr2 n n2) (i + 2)
--LIQUID           | otherwise                  = Yield (unsafeChr n) (i + 1)
--LIQUID           where
--LIQUID             n  = A.unsafeIndex arr i
--LIQUID             n2 = A.unsafeIndex arr (i + 1)
{-# INLINE [0] stream #-}

-- | /O(n)/ Convert a 'Text' into a 'Stream Char', but iterate
-- backwards.
reverseStream :: Text -> Stream Char
reverseStream (Text arr off len) = Stream next (off+len-1) (maxSize len)
    where
      {-# INLINE next #-}
      next !i
          | i < off   = Done
          | otherwise =
              let n  = A.unsafeIndexB arr off len i
              in if n >= 0xDC00 && n <= 0xDFFF
                 then let n2 = A.unsafeIndex arr (i - 1)
                      in Yield (U16.chr2 n2 n) (i - 2)
                 else Yield (unsafeChr n) (i - 1)
--LIQUID           | n >= 0xDC00 && n <= 0xDFFF = Yield (U16.chr2 n2 n) (i - 2)
--LIQUID           | otherwise                  = Yield (unsafeChr n) (i - 1)
--LIQUID           where
--LIQUID             n  = A.unsafeIndex arr i
--LIQUID             n2 = A.unsafeIndex arr (i - 1)
{-# INLINE [0] reverseStream #-}

-- | /O(n)/ Convert a 'Stream Char' into a 'Text'.
--LIQUID FIXME: we should be able to prove these streaming functions terminating
--              but that requires giving a refined Stream type, which requires
--              handling existential types.
{-@ Lazy unstream @-}
unstream :: Stream Char -> Text
unstream (Stream next0 s0 len) = runText $ \done -> do
  let mlen = upperBound 4 len
  arr0 <- A.new mlen
  let outer arr top = loop
       where
        loop !s !i =
            case next0 s of
              Done          -> done arr i
              Skip s'       -> loop s' i
              Yield x s'
                | j >= top  -> {-# SCC "unstream/resize" #-} do
                               let top' = (top + 1) * 2 --LIQUID `shiftL` 1
                               arr' <- A.new top'
                               A.copyM arr' 0 arr 0 top
                               outer arr' top' s i
                | otherwise -> do d <- unsafeWrite arr i x
                                  loop s' (i+d)
                where j | ord x < 0x10000 = i
                        | otherwise       = i + 1
  outer arr0 mlen s0 0
{-# INLINE [0] unstream #-}
{-# RULES "STREAM stream/unstream fusion" forall s. stream (unstream s) = s #-}


-- ----------------------------------------------------------------------------
-- * Basic stream functions

length :: Stream Char -> Int
length = S.lengthI
{-# INLINE[0] length #-}

-- | /O(n)/ Reverse the characters of a string.
{-@ Lazy reverse @-}
reverse :: Stream Char -> Text
reverse (Stream next s len0)
    | isEmpty len0 = I.empty
    | otherwise    = let len0' = upper 4 len0 --LIQUID INLINE upperBound 4 (larger len0 4)
                         (arr, (off', len')) = A.run2 (A.new len0' >>= loop s (len0'-1) len0')
                     in I.textP arr (liquidAssume (off' <= A.aLen arr) off')
                                    (liquidAssume (off' + len' <= A.aLen arr) len')
  where
    upper k (Exact n) = max k n
    upper k (Max   n) = max k n
    upper k _         = k
    --LIQUID SCOPE len0' = upperBound 4 (larger len0 4)
    --LIQUID SCOPE (arr, (off', len')) = A.run2 (A.new len0' >>= reverse_loop s (len0'-1) len0')
    loop !s0 !i !len marr =
        case next s0 of
          Done -> return (marr, (j, len-j))
              where j = i + 1
          Skip s1    -> loop s1 i len marr
          Yield x s1 | i < least -> {-# SCC "reverse/resize" #-} do
                       let newLen = len * 2 --LIQUID `shiftL` 1
                       marr' <- A.new newLen
                       A.copyM marr' (newLen-len) marr 0 len
                       write s1 (len+i) newLen marr'
                     | otherwise -> write s1 i len marr
            where n = ord x
                  least | n < 0x10000 = 0
                        | otherwise   = 1
                  m = n - 0x10000
                  lo = fromIntegral $ (m `shiftR` 10) + 0xD800
                  hi = fromIntegral $ (m .&. 0x3FF) + 0xDC00
                  write t j l mar
                      | n < 0x10000 = do
                          A.unsafeWrite mar j (fromIntegral n)
                          loop t (j-1) l mar
                      | otherwise = do
                          A.unsafeWrite mar (j-1) lo
                          A.unsafeWrite mar j hi
                          loop t (j-2) l mar
{-# INLINE [0] reverse #-}

-- | /O(n)/ Perform the equivalent of 'scanr' over a list, only with
-- the input and result reversed.
reverseScanr :: (Char -> Char -> Char) -> Char -> Stream Char -> Stream Char
reverseScanr f z0 (Stream next0 s0 len) = Stream next (S1 :*: z0 :*: s0) (len+1) -- HINT maybe too low
  where
    {-# INLINE next #-}
    next (S1 :*: z :*: s) = Yield z (S2 :*: z :*: s)
    next (S2 :*: z :*: s) = case next0 s of
                              Yield x s' -> let !x' = f x z
                                            in Yield x' (S2 :*: x' :*: s')
                              Skip s'    -> Skip (S2 :*: z :*: s')
                              Done       -> Done
{-# INLINE reverseScanr #-}

-- | /O(n)/ Like 'unfoldr', 'unfoldrN' builds a stream from a seed
-- value. However, the length of the result is limited by the
-- first argument to 'unfoldrN'. This function is more efficient than
-- 'unfoldr' when the length of the result is known.
unfoldrN :: Int -> (a -> Maybe (Char,a)) -> a -> Stream Char
unfoldrN n = S.unfoldrNI n
{-# INLINE [0] unfoldrN #-}

-------------------------------------------------------------------------------
-- ** Indexing streams

-- | /O(n)/ stream index (subscript) operator, starting from 0.
index :: Stream Char -> Int -> Char
index = S.indexI
{-# INLINE [0] index #-}

-- | The 'findIndex' function takes a predicate and a stream and
-- returns the index of the first element in the stream
-- satisfying the predicate.
findIndex :: (Char -> Bool) -> Stream Char -> Maybe Int
findIndex = S.findIndexI
{-# INLINE [0] findIndex #-}

-- | /O(n)/ The 'count' function returns the number of times the query
-- element appears in the given stream.
countChar :: Char -> Stream Char -> Int
countChar = S.countCharI
{-# INLINE [0] countChar #-}

-- | /O(n)/ Like a combination of 'map' and 'foldl''. Applies a
-- function to each element of a 'Text', passing an accumulating
-- parameter from left to right, and returns a final 'Text'.
{-@ Lazy mapAccumL @-}
mapAccumL :: (a -> Char -> (a,Char)) -> a -> Stream Char -> (a, Text)
mapAccumL f z0 (Stream next0 s0 len) =
    (nz,I.textP na 0 nl)
  where
    --LIQUID INLINE (na,(nz,nl)) = A.run2 (A.new mlen >>= \arr -> outer arr mlen z0 s0 0)
    (na,(nz,nl)) = runST $ do (marr,x) <- (A.new mlen >>= \arr -> outer arr mlen z0 s0 0)
                              arr <- A.unsafeFreeze marr
                              return (arr,x)
      where mlen = upperBound 4 len
    outer arr top = loop
      where
        loop !z !s !i =
            case next0 s of
              Done          -> return (arr, (z,i))
              Skip s'       -> loop z s' i
              Yield x s'
                | j >= top  -> {-# SCC "mapAccumL/resize" #-} do
                               let top' = (top + 1) * 2 --LIQUID `shiftL` 1
                               arr' <- A.new top'
                               A.copyM arr' 0 arr 0 top
                               outer arr' top' z s i
                --LIQUID BUG | otherwise -> do let (z',c) = f z x
                --LIQUID BUG                   d <- unsafeWrite arr i c
                --LIQUID BUG                   loop z' s' (i+d)
                --LIQUID BUG where j | ord x < 0x10000 = i
                --LIQUID BUG         | otherwise       = i + 1
                --LIQUID this needs to be `ord c` because `f` may return a Char
                --LIQUID that takes 2 slots in the array. see LIQUID.txt for details
                | otherwise -> do d <- unsafeWrite arr i c
                                  loop z' s' (i+d)
                where (z',c) = f z x
                      j | ord c < 0x10000 = i
                        | otherwise       = i + 1
{-# INLINE [0] mapAccumL #-}
