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
import Data.Text.Private (runText
                         --LIQUID
                         , Iter(..))
import Data.Text.UnsafeChar (ord, unsafeChr, unsafeWrite)
import Data.Text.UnsafeShift (shiftL, shiftR)
import qualified Data.Text.Array as A
import qualified Data.Text.Fusion.Common as S
import Data.Text.Fusion.Internal
import Data.Text.Fusion.Size
import qualified Data.Text.Internal as I
import qualified Data.Text.Encoding.Utf16 as U16

--LIQUID
import qualified Data.Text.Array
import qualified Data.Text.Private
import qualified Data.Word
import qualified GHC.ST
import qualified GHC.Types
import Prelude (Integer, Integral)
import Language.Haskell.Liquid.Prelude


default(Int)

{-@ qualif LTPlus(v:int, a:int, b:int) : v < (a + b) @-}
{-@ qualif LTEPlus(v:int, a:int, b:int) : (v + a) <= b @-}

--LIQUID FIXME: why aren't these qualifiers instantiated when the same quals are mined from foo and bar??
{- qualif OrdC(v:int, x:GHC.Types.Char) : (((One x) => (v = 0)) && ((Two x) => (v = 1))) @-}
{- qualif OrdInt(v:int, i:int, x:GHC.Types.Char) : (((One x) => (v = i)) && ((Two x) => (v = (i + 1)))) @-}

{-@ foo :: x:Char
        -> i:Nat
        -> {v:Nat | (((One x) => (v = i)) && ((Two x) => (v = (i + 1))))}
  @-}
foo :: Char -> Int -> Int
foo x i | ord x < 0x10000 = i
        | otherwise       = i + 1
{-@ bar :: x:Char
        -> {v:Nat | (((One x) => (v = 0)) && ((Two x) => (v = 1)))}
  @-}
bar :: Char -> Int
bar x | ord x < 0x10000 = 0
      | otherwise       = 1


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
unstream :: Stream Char -> Text
unstream (Stream next0 s0 len) = runText $ \done -> do
  let mlen = upperBound 4 len
  arr0 <- A.new mlen
  -- let outer arr top = loop
  --      where
  --       loop !s !i =
  --           case next0 s of
  --             Done          -> done arr i
  --             Skip s'       -> loop s' i
  --             Yield x s'
  --               | j >= top  -> {-# SCC "unstream/resize" #-} do
  --                              let top' = (top + 1) * 2 --LIQUID `shiftL` 1
  --                              arr' <- A.new top'
  --                              A.copyM arr' 0 arr 0 top
  --                              outer arr' top' s i
  --               | otherwise -> do d <- unsafeWrite arr i x
  --                                 loop s' (i+d)
  --               where j | ord x < 0x10000 = i
  --                       | otherwise       = i + 1
  unstream_outer arr0 mlen done next0 s0 0
{-@ unstream_outer :: ma:Data.Text.Array.MArray s
          -> top:{v:Nat | v = (malen ma)}
          -> (ma1:Data.Text.Array.MArray s
              -> {v:Nat | v <= (malen ma1)}
              -> GHC.ST.ST s Data.Text.Internal.Text)
          -> (a -> Data.Text.Fusion.Internal.Step a Char)
          -> a
          -> i:{v:Nat | v <= top}
          -> GHC.ST.ST s Data.Text.Internal.Text
  @-}
unstream_outer :: A.MArray s -> Int -> (A.MArray s -> Int -> GHC.ST.ST s Text) -> (a -> Step a Char) -> a -> Int -> GHC.ST.ST s Text
unstream_outer arr top done next0 = loop
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
                               unstream_outer arr' top' done next0 s i
                | otherwise -> do d <- unsafeWrite arr i x
                                  loop s' (i+d)
                where j | ord x < 0x10000 = i
                        | otherwise       = i + 1
{-# INLINE [0] unstream #-}
{-# RULES "STREAM stream/unstream fusion" forall s. stream (unstream s) = s #-}


-- ----------------------------------------------------------------------------
-- * Basic stream functions

length :: Stream Char -> Int
length = S.lengthI
{-# INLINE[0] length #-}

-- | /O(n)/ Reverse the characters of a string.
reverse :: Stream Char -> Text
reverse (Stream next s len0)
    | isEmpty len0 = I.empty
    | otherwise    = let len0' = upper 4 len0 --LIQUID upperBound 4 (larger len0 4)
                         (arr, (off', len')) = A.run2 (A.new len0' >>= reverse_loop next s (len0'-1) len0')
                     in I.textP arr (liquidAssume (off' <= A.aLen arr) off')
                                    (liquidAssume (off' + len' <= A.aLen arr) len')
  where
    upper k (Exact n) = max k n
    upper k (Max   n) = max k n
    upper k _         = k
    -- len0' = upperBound 4 (larger len0 4)
    -- (arr, (off', len')) = A.run2 (A.new len0' >>= reverse_loop s (len0'-1) len0')
    -- loop !s0 !i !len marr =
    --     case next s0 of
    --       Done -> return (marr, (j, len-j))
    --           where j = i + 1
    --       Skip s1    -> loop s1 i len marr
    --       Yield x s1 | i < least -> {-# SCC "reverse/resize" #-} do
    --                    let newLen = len * 2 --LIQUID `shiftL` 1
    --                    marr' <- A.new newLen
    --                    A.copyM marr' (newLen-len) marr 0 len
    --                    write s1 (len+i) newLen marr'
    --                  | otherwise -> write s1 i len marr
    --         where n = ord x
    --               least | n < 0x10000 = 0
    --                     | otherwise   = 1
    --               m = n - 0x10000
    --               lo = fromIntegral $ (m `shiftR` 10) + 0xD800
    --               hi = fromIntegral $ (m .&. 0x3FF) + 0xDC00
    --               write t j l mar
    --                   | n < 0x10000 = do
    --                       A.unsafeWrite mar j (fromIntegral n)
    --                       loop t (j-1) l mar
    --                   | otherwise = do
    --                       A.unsafeWrite mar (j-1) lo
    --                       A.unsafeWrite mar j hi
    --                       loop t (j-2) l mar
{-# INLINE [0] reverse #-}

{-@ reverse_loop :: (a -> Step a Char) -> a
                 -> i:{v:Int | v >= -1}
                 -> len:{v:Int | ((v >= 4) && (v > i))}
                 -> {v:A.MArray s | (malen v) = len}
                 -> GHC.ST.ST s ((A.MArray s), (Nat, Nat))<{\a p ->
                         (((fst p) <= (malen a)) && (((fst p) + (snd p)) <= (malen a)))}>
  @-}
reverse_loop :: (a -> Step a Char) -> a -> Int -> Int -> A.MArray s
             -> GHC.ST.ST s ((A.MArray s), (Int, Int))
reverse_loop next !s0 !i !len marr =
    case next s0 of
      Done -> return (marr, (j, len-j))
          where j = i + 1
      Skip s1    -> reverse_loop next s1 i len marr
      Yield x s1 | i < least -> {-# SCC "reverse/resize" #-} do
                   let newLen = len + len --LIQUID `shiftL` 1
                   marr' <- A.new newLen
                   A.copyM marr' (newLen-len) marr 0 len
                   reverse_write s1 (len+i) newLen marr' x next
                 | otherwise -> reverse_write s1 i len marr x next
        where n = ord x
              least | n < 0x10000 = 0
                    | otherwise   = 1

{-@ reverse_write :: a
                  -> j:Nat
                  -> l:{v:Int | ((v >= 4) && (v > j))}
                  -> mar:{v:A.MArray s | (malen v) = l}
                  -> x:{v:Char | (((One v) => (j >= 0))
                               && ((Two v) => (j >= 1)))}
                  -> (a -> Step a Char)
                  -> GHC.ST.ST s ((A.MArray s), (Nat, Nat))<{\a p ->
                         (((fst p) <= (malen a)) && (((fst p) + (snd p)) <= (malen a)))}>
  @-}
reverse_write :: a -> Int -> Int -> A.MArray s -> Char -> (a -> Step a Char)
              -> GHC.ST.ST s ((A.MArray s), (Int, Int))
reverse_write t j l mar x next
    | n < 0x10000 = do
        A.unsafeWrite mar j (fromIntegral n)
        reverse_loop next t (j-1) l mar
    | otherwise = do
        A.unsafeWrite mar (j-1) lo
        A.unsafeWrite mar j hi
        reverse_loop next t (j-2) l mar
    where n = ord x
          m = n - 0x10000
          lo = fromIntegral $ (m `shiftR` 10) + 0xD800
          hi = fromIntegral $ (m .&. 0x3FF) + 0xDC00

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
mapAccumL :: (a -> Char -> (a,Char)) -> a -> Stream Char -> (a, Text)
mapAccumL f z0 (Stream next0 s0 len) =
    (nz,I.textP na 0 (liquidAssume (nl <= A.aLen na) nl))
  where
    (na,(nz,nl)) = A.run2 (A.new mlen >>= \arr -> mapAccumL_outer f next0 arr mlen z0 s0 0)
    -- (na,(nz,nl)) = A.run2 (A.new mlen >>= \arr -> outer arr mlen z0 s0 0)
      where mlen = upperBound 4 len
    -- outer arr top = loop
    --   where
    --     loop !z !s !i =
    --         case next0 s of
    --           Done          -> return (arr, (z,i))
    --           Skip s'       -> loop z s' i
    --           Yield x s'
    --             | j >= top  -> {-# SCC "mapAccumL/resize" #-} do
    --                            let top' = (top + 1) * 2 --LIQUID `shiftL` 1
    --                            arr' <- A.new top'
    --                            A.copyM arr' 0 arr 0 top
    --                            outer arr' top' z s i
    --             | otherwise -> do let (z',c) = f z x
    --                               d <- unsafeWrite arr i c
    --                               loop z' s' (i+d)
    --             where j | ord x < 0x10000 = i
    --                     | otherwise       = i + 1
{-@ mapAccumL_outer :: (a -> Char -> (a,Char))
                    -> (b -> Step b Char)
                    -> ma:A.MArray s
                    -> top:{v:Int | v = (malen ma)}
                    -> a
                    -> b
                    -> i:{v:Nat | v <= top}
                    -> GHC.ST.ST s (A.MArray s, (a, Nat))<{\a p -> (snd p) <= (malen a)}>
  @-}
mapAccumL_outer :: (a -> Char -> (a,Char))
                -> (b -> Step b Char)
                -> A.MArray s
                -> Int
                -> a
                -> b
                -> Int
                -> GHC.ST.ST s (A.MArray s, (a, Int))
mapAccumL_outer f next0 arr top = loop
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
                             mapAccumL_outer f next0 arr' top' z s i
              | otherwise -> do d <- unsafeWrite arr i c
                                loop z' s' (i+d)
              --LIQUID this needs to be `ord c` because `f` may return a Char
              --LIQUID that takes 2 slots in the array. see LIQUID.txt for details
              where (z',c) = f z x
                    j | ord c < 0x10000 = i
                      | otherwise       = i + 1
{-# INLINE [0] mapAccumL #-}
