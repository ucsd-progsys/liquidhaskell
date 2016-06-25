{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}

-- ---------------------------------------------------------------------------
-- |
-- Module      : Data.Vector.Algorithms.AmericanFlag
-- Copyright   : (c) 2011 Dan Doel
-- Maintainer  : Dan Doel <dan.doel@gmail.com>
-- Stability   : Experimental
-- Portability : Non-portable (FlexibleContexts, ScopedTypeVariables)
--
-- This module implements American flag sort: an in-place, unstable, bucket
-- sort. Also in contrast to radix sort, the values are inspected in a big
-- endian order, and buckets are sorted via recursive splitting. This,
-- however, makes it sensible for sorting strings in lexicographic order
-- (provided indexing is fast).
--
-- The algorithm works as follows: at each stage, the array is looped over,
-- counting the number of elements for each bucket. Then, starting at the
-- beginning of the array, elements are permuted in place to reside in the
-- proper bucket, following chains until they reach back to the current
-- base index. Finally, each bucket is sorted recursively. This lends itself
-- well to the aforementioned variable-length strings, and so the algorithm
-- takes a stopping predicate, which is given a representative of the stripe,
-- rather than running for a set number of iterations.

module Data.Vector.Algorithms.AmericanFlag ( sort
                                           , sortBy
                                           , Lexicographic(..)
                                           ) where

import Prelude hiding (read, length)

import Control.Monad
import Control.Monad.Primitive

import Data.Word
import Data.Int
import Data.Bits

import qualified Data.ByteString as B

import Data.Vector.Generic.Mutable
import qualified Data.Vector.Primitive.Mutable as PV

import qualified Data.Vector.Unboxed.Mutable as U

import Data.Vector.Algorithms.Common

import qualified Data.Vector.Algorithms.Insertion as I
import Language.Haskell.Liquid.Prelude (liquidAssume)

-- | The methods of this class specify the information necessary to sort
-- arrays using the default ordering. The name 'Lexicographic' is meant
-- to convey that index should return results in a similar way to indexing
-- into a string.
class Lexicographic e where
  -- | Given a representative of a stripe and an index number, this
  -- function should determine whether to stop sorting.
  terminate :: e -> Int -> Bool
  -- | The size of the bucket array necessary for sorting es
  size      :: e -> Int
  -- | Determines which bucket a given element should inhabit for a
  -- particular iteration.
  index     :: Int -> e -> Int


-- | LIQUID Class Specification ---------------------------------------------

{-@ measure lexSize :: a -> Int                                           @-}
{-@ size  :: (Lexicographic e) => x:e -> {v:Nat | v = (lexSize x)}        @-}
{-@ index :: (Lexicographic e) => Int -> x:e -> {v:Nat | v < (lexSize x)} @-}
{-@ terminate :: (Lexicographic e) => x:e -> n:Int
              -> {v:Bool | (((n+1) >= maxPasses) => (Prop v))}
  @-}

{-@ measure maxPasses :: Int @-}
{-@ maxPasses :: {v:Nat | v = maxPasses} @-}
maxPasses :: Int
maxPasses = undefined
{-@ qualif MaxPasses(v:int, p:int): v = (maxPasses-p) @-}
{-@ qualif MaxPasses(v:int): v <= maxPasses @-}
{-@ qualif MaxPasses(v:int): v < maxPasses @-}


instance Lexicographic Word8 where
  terminate _ n = n > 0
  {-# INLINE terminate #-}
  size _ = 256
  {-# INLINE size #-}
  index _ n = fromIntegral n
  {-# INLINE index #-}

instance Lexicographic Word16 where
  terminate _ n = n > 1
  {-# INLINE terminate #-}
  size _ = 256
  {-# INLINE size #-}
  index 0 n = fromIntegral $ (n `shiftR`  8) .&. 255
  index 1 n = fromIntegral $ n .&. 255
  index _ _ = 0
  {-# INLINE index #-}

instance Lexicographic Word32 where
  terminate _ n = n > 3
  {-# INLINE terminate #-}
  size _ = 256
  {-# INLINE size #-}
  index 0 n = fromIntegral $ (n `shiftR` 24) .&. 255
  index 1 n = fromIntegral $ (n `shiftR` 16) .&. 255
  index 2 n = fromIntegral $ (n `shiftR`  8) .&. 255
  index 3 n = fromIntegral $ n .&. 255
  index _ _ = 0
  {-# INLINE index #-}

instance Lexicographic Word64 where
  terminate _ n = n > 7
  {-# INLINE terminate #-}
  size _ = 256
  {-# INLINE size #-}
  index 0 n = fromIntegral $ (n `shiftR` 56) .&. 255
  index 1 n = fromIntegral $ (n `shiftR` 48) .&. 255
  index 2 n = fromIntegral $ (n `shiftR` 40) .&. 255
  index 3 n = fromIntegral $ (n `shiftR` 32) .&. 255
  index 4 n = fromIntegral $ (n `shiftR` 24) .&. 255
  index 5 n = fromIntegral $ (n `shiftR` 16) .&. 255
  index 6 n = fromIntegral $ (n `shiftR`  8) .&. 255
  index 7 n = fromIntegral $ n .&. 255
  index _ _ = 0
  {-# INLINE index #-}

instance Lexicographic Word where
  terminate _ n = n > 7
  {-# INLINE terminate #-}
  size _ = 256
  {-# INLINE size #-}
  index 0 n = fromIntegral $ (n `shiftR` 56) .&. 255
  index 1 n = fromIntegral $ (n `shiftR` 48) .&. 255
  index 2 n = fromIntegral $ (n `shiftR` 40) .&. 255
  index 3 n = fromIntegral $ (n `shiftR` 32) .&. 255
  index 4 n = fromIntegral $ (n `shiftR` 24) .&. 255
  index 5 n = fromIntegral $ (n `shiftR` 16) .&. 255
  index 6 n = fromIntegral $ (n `shiftR`  8) .&. 255
  index 7 n = fromIntegral $ n .&. 255
  index _ _ = 0
  {-# INLINE index #-}

instance Lexicographic Int8 where
  terminate _ n = n > 0
  {-# INLINE terminate #-}
  size _ = 256
  {-# INLINE size #-}
  index _ n = 255 .&. fromIntegral n `xor` 128
  {-# INLINE index #-}

instance Lexicographic Int16 where
  terminate _ n = n > 1
  {-# INLINE terminate #-}
  size _ = 256
  {-# INLINE size #-}
  index 0 n = fromIntegral $ ((n `xor` minBound) `shiftR` 8) .&. 255
  index 1 n = fromIntegral $ n .&. 255
  index _ _ = 0
  {-# INLINE index #-}

instance Lexicographic Int32 where
  terminate _ n = n > 3
  {-# INLINE terminate #-}
  size _ = 256
  {-# INLINE size #-}
  index 0 n = fromIntegral $ ((n `xor` minBound) `shiftR` 24) .&. 255
  index 1 n = fromIntegral $ (n `shiftR` 16) .&. 255
  index 2 n = fromIntegral $ (n `shiftR`  8) .&. 255
  index 3 n = fromIntegral $ n .&. 255
  index _ _ = 0
  {-# INLINE index #-}

instance Lexicographic Int64 where
  terminate _ n = n > 7
  {-# INLINE terminate #-}
  size _ = 256
  {-# INLINE size #-}
  index 0 n = fromIntegral $ ((n `xor` minBound) `shiftR` 56) .&. 255
  index 1 n = fromIntegral $ (n `shiftR` 48) .&. 255
  index 2 n = fromIntegral $ (n `shiftR` 40) .&. 255
  index 3 n = fromIntegral $ (n `shiftR` 32) .&. 255
  index 4 n = fromIntegral $ (n `shiftR` 24) .&. 255
  index 5 n = fromIntegral $ (n `shiftR` 16) .&. 255
  index 6 n = fromIntegral $ (n `shiftR`  8) .&. 255
  index 7 n = fromIntegral $ n .&. 255
  index _ _ = 0
  {-# INLINE index #-}

instance Lexicographic Int where
  terminate _ n = n > 7
  {-# INLINE terminate #-}
  size _ = 256
  {-# INLINE size #-}
  index 0 n = ((n `xor` minBound) `shiftR` 56) .&. 255
  index 1 n = (n `shiftR` 48) .&. 255
  index 2 n = (n `shiftR` 40) .&. 255
  index 3 n = (n `shiftR` 32) .&. 255
  index 4 n = (n `shiftR` 24) .&. 255
  index 5 n = (n `shiftR` 16) .&. 255
  index 6 n = (n `shiftR`  8) .&. 255
  index 7 n = n .&. 255
  index _ _ = 0
  {-# INLINE index #-}

instance Lexicographic B.ByteString where
  terminate b i = i >= B.length b
  {-# INLINE terminate #-}
  size _ = 257
  {-# INLINE size #-}
  index i b
    | i >= B.length b = 0
    | i < 0           = 0  -- JHALA: otherwise error!
    | otherwise       = fromIntegral (B.index b i) + 1
  {-# INLINE index #-}

-- | Sorts an array using the default ordering. Both Lexicographic and
-- Ord are necessary because the algorithm falls back to insertion sort
-- for sufficiently small arrays.
sort :: forall e m v. (PrimMonad m, MVector v e, Lexicographic e, Ord e)
     => v (PrimState m) e -> m ()
sort v = sortBy compare terminate (size e) index maxPasses v
 where e :: e
       e = undefined
{-# INLINABLE sort #-}

-- | A fully parameterized version of the sorting algorithm. Again, this
-- function takes both radix information and a comparison, because the
-- algorithms falls back to insertion sort for small arrays.

{-@ sortBy :: (PrimMonad m, MVector v e)
       => (Comparison e)
       -> (e -> n:Int -> {v:Bool | (((n+1) >= maxPasses) => (Prop v) )})
       -> buckets:Nat
       -> (Int -> e -> {v:Nat | v < buckets})
       -> {v:Nat | v = maxPasses}
       -> v (PrimState m) e
       -> m ()
  @-}
sortBy :: (PrimMonad m, MVector v e)
       => Comparison e       -- ^ a comparison for the insertion sort flalback
       -> (e -> Int -> Bool) -- ^ determines whether a stripe is complete
       -> Int                -- ^ the number of buckets necessary
       -> (Int -> e -> Int)  -- ^ the big-endian radix function
       -> Int
       -> v (PrimState m) e  -- ^ the array to be sorted
       -> m ()
sortBy cmp stop buckets radix mp v
  | length v == 0 = return ()
  | otherwise     = do count <- new buckets
                       pile <- new buckets
                       countLoop v count (radix 0) 
                       flagLoop cmp stop count pile v mp radix
{-# INLINE sortBy #-}

flagLoop :: (PrimMonad m, MVector v e)
         => Comparison e
         -> (e -> Int -> Bool)           -- number of passes
         -> PV.MVector (PrimState m) Int -- auxiliary count array
         -> PV.MVector (PrimState m) Int -- auxiliary pile array
         -> v (PrimState m) e            -- source array
         -> Int
         -> (Int -> e -> Int)            -- radix function
         -> m ()
flagLoop cmp stop count pile v mp radix = go 0 v (mp) 1
 where

 {-@ Decrease go 3 4 @-}
  {- LIQUID WITNESS -}
 go pass v (d :: Int) (_ :: Int)
   = do e <- unsafeRead v 0
        if (stop e $ pass - 1)
          then return ()
          else go' pass v (mp-pass) 0
        --LIQUID INLINE unless (stop e $ pass - 1) $ go' pass v (mp-pass) 0

 {-@ Decrease go' 3 4 @-}
   {- LIQUID WITNESS -}
 go' pass v (d :: Int) (_ :: Int)
   | len < threshold = I.sortByBounds cmp v 0 len
   | otherwise       = do accumulate count pile
                          permute count pile v (radix pass) 
                          recurse len 0
  where
  len = length v
  ppass = pass + 1

  {- LIQUID WITNESS -}
  recurse (twit :: Int) i
    | i < len   = do j <- countStripe count v (radix ppass) (radix pass) i
                     go ppass (unsafeSlice i (j - i) v) (mp-ppass) 1
                     recurse (len - j) j
    | otherwise = return ()
{-# INLINE flagLoop #-}

accumulate :: (PrimMonad m)
           => PV.MVector (PrimState m) Int
           -> PV.MVector (PrimState m) Int
           -> m ()
accumulate count pile = loop len 0 0
 where
 len = length count

  {- LIQUID WITNESS -}
 loop (twit :: Int) i acc
   | i < len = do ci <-  unsafeRead count i
                  let acc' = acc + ci
                  unsafeWrite pile i acc
                  unsafeWrite count i acc'
                  loop (twit - 1) (i+1) acc'
   | otherwise    = return ()
{-# INLINE accumulate #-}

permute :: (PrimMonad m, MVector v e)
        => PV.MVector (PrimState m) Int     -- count array
        -> PV.MVector (PrimState m) Int     -- pile array
        -> v (PrimState m) e                -- source array
        -> (e -> Int)                       -- radix function
        -> m ()
permute count pile v rdx = go len 0
 where
 len = length v

  {- LIQUID WITNESS -}
 go (twit::Int) i
   | i < len   = do e <- unsafeRead v i
                    let r = rdx e
                    p <- unsafeRead pile r
                    m <- if r > 0
                            then unsafeRead count (r-1)
                            else return 0
                    case () of
                      -- if the current element is alunsafeReady in the right pile,
                      -- go to the end of the pile
                      _ | m <= i && i < p  -> if p < len then go (len - p) p else return ()
                      -- if the current element happens to be in the right
                      -- pile, bump the pile counter and go to the next element
                        | i == p           -> unsafeWrite pile r (p+1) >> go (len - (i+1)) (i+1)
                      -- otherwise follow the chain
                        | otherwise        -> follow (len - p) i e p >> go (len - (i+1)) (i+1)
   | otherwise = return ()

  {- LIQUID WITNESS -}
 follow (twit :: Int) i e j'
               = do let j = liquidAssume (0 <= j' && j' < len) j' -- LIQUID: not sure why this holds, has to do with `inc`
                    en <- unsafeRead v j
                    let r = rdx en
                    p <- inc pile r
                    if p == j
                      -- if the target happens to be in the right pile, don't move it.
                      then follow (len - (j+1)) i e (j+1)
                      else unsafeWrite v j e >> if i == p
                                                then unsafeWrite v i en
                                                else let p'' = liquidAssume (j < p && p < len) p in 
                                                     follow (len - p'') i en p''
{-# INLINE permute #-}

countStripe :: (PrimMonad m, MVector v e)
            => PV.MVector (PrimState m) Int -- count array
            -> v (PrimState m) e            -- source array
            -> (e -> Int)                   -- radix function
            -> (e -> Int)                   -- stripe function
            -> Int                          -- starting position
            -> m Int                        -- end of stripe: [lo,hi)
countStripe count v rdx str lo = do set count 0
                                    e <- unsafeRead v lo
                                    go (len - (lo + 1)) (str e) e (lo+1)
 where
 len = length v
  {- LIQUID WITNESS -}
 go (twit :: Int) !s e i
    = inc count (rdx e) >>
             if i < len
               then do en <- unsafeRead v i
                       if str en == s
                          then go (len - (i+1)) s en (i+1)
                          else return i
               else return len
{-# INLINE countStripe #-}

threshold :: Int
threshold = 25

