{-# LANGUAGE Rank2Types, MultiParamTypeClasses, FlexibleContexts,
             TypeFamilies, ScopedTypeVariables, BangPatterns, CPP #-}
-- |
-- Module      : Data.Vector.Generic
-- Copyright   : (c) Roman Leshchinskiy 2008-2010
-- License     : BSD-style
--
-- Maintainer  : Roman Leshchinskiy <rl@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable
-- 
-- Generic interface to pure vectors.
--

module Data.Vector.Generic (
  -- * Immutable vectors
  Vector(..), Mutable,

  -- * Accessors

  -- ** Length information
  length, null,

  -- ** Indexing
  (!), (!?), head, last,
  unsafeIndex, unsafeHead, unsafeLast,

  -- ** Monadic indexing
  indexM, headM, lastM,
  unsafeIndexM, unsafeHeadM, unsafeLastM,

  -- ** Extracting subvectors (slicing)
  slice, init, tail, take, drop, splitAt,
  unsafeSlice, unsafeInit, unsafeTail, unsafeTake, unsafeDrop,

  -- * Construction

  -- ** Initialisation
  empty, singleton, replicate, generate, iterateN,

  -- ** Monadic initialisation
  replicateM, generateM, create,

  -- ** Unfolding
  unfoldr, unfoldrN,
  constructN, constructrN,

  -- ** Enumeration
  enumFromN, enumFromStepN, enumFromTo, enumFromThenTo,

  -- ** Concatenation
  cons, snoc, (++), concat,

  -- ** Restricting memory usage
  force,

  -- * Modifying vectors

  -- ** Bulk updates
  (//), update, update_,
  unsafeUpd, unsafeUpdate, unsafeUpdate_,

  -- ** Accumulations
  accum, accumulate, accumulate_,
  unsafeAccum, unsafeAccumulate, unsafeAccumulate_,

  -- ** Permutations 
  reverse, backpermute, unsafeBackpermute,

  -- ** Safe destructive updates
  modify,

  -- * Elementwise operations

  -- ** Indexing
  indexed,

  -- ** Mapping
  map, imap, concatMap,

  -- ** Monadic mapping
  mapM, mapM_, forM, forM_,

  -- ** Zipping
  zipWith, zipWith3, zipWith4, zipWith5, zipWith6,
  izipWith, izipWith3, izipWith4, izipWith5, izipWith6,
  zip, zip3, zip4, zip5, zip6,

  -- ** Monadic zipping
  zipWithM, zipWithM_,

  -- ** Unzipping
  unzip, unzip3, unzip4, unzip5, unzip6,

  -- * Working with predicates

  -- ** Filtering
  filter, ifilter, filterM,
  takeWhile, dropWhile,

  -- ** Partitioning
  partition, unstablePartition, span, break,

  -- ** Searching
  elem, notElem, find, findIndex, findIndices, elemIndex, elemIndices,

  -- * Folding
  foldl, foldl1, foldl', foldl1', foldr, foldr1, foldr', foldr1',
  ifoldl, ifoldl', ifoldr, ifoldr',

  -- ** Specialised folds
  all, any, and, or,
  sum, product,
  maximum, maximumBy, minimum, minimumBy,
  minIndex, minIndexBy, maxIndex, maxIndexBy,

  -- ** Monadic folds
  foldM, foldM', fold1M, fold1M',
  foldM_, foldM'_, fold1M_, fold1M'_,

  -- ** Monadic sequencing
  sequence, sequence_,

  -- * Prefix sums (scans)
  prescanl, prescanl',
  postscanl, postscanl',
  scanl, scanl', scanl1, scanl1',
  prescanr, prescanr',
  postscanr, postscanr',
  scanr, scanr', scanr1, scanr1',

  -- * Conversions

  -- ** Lists
  toList, fromList, fromListN,

  -- ** Different vector types
  convert,

  -- ** Mutable vectors
  freeze, thaw, copy, unsafeFreeze, unsafeThaw, unsafeCopy,

  -- * Fusion support

  -- ** Conversion to/from Streams
  stream, unstream, streamR, unstreamR,

  -- ** Recycling support
  new, clone,

  -- * Utilities

  -- ** Comparisons
  eq, cmp,

  -- ** Show and Read
  showsPrec, readPrec,

  -- ** @Data@ and @Typeable@
  gfoldl, dataCast, mkType
) where

import           Data.Vector.Generic.Base

import           Data.Vector.Generic.Mutable ( MVector )
import qualified Data.Vector.Generic.Mutable as M

import qualified Data.Vector.Generic.New as New
import           Data.Vector.Generic.New ( New )

import qualified Data.Vector.Fusion.Stream as Stream
import           Data.Vector.Fusion.Stream ( Stream, MStream, Step(..), inplace, liftStream )
import qualified Data.Vector.Fusion.Stream.Monadic as MStream
import           Data.Vector.Fusion.Stream.Size
import           Data.Vector.Fusion.Util

import Control.Monad.ST ( ST, runST )
import Control.Monad.Primitive
import qualified Control.Monad as Monad
import qualified Data.List as List
import Prelude hiding ( length, null,
                        replicate, (++), concat,
                        head, last,
                        init, tail, take, drop, splitAt, reverse,
                        map, concat, concatMap,
                        zipWith, zipWith3, zip, zip3, unzip, unzip3,
                        filter, takeWhile, dropWhile, span, break,
                        elem, notElem,
                        foldl, foldl1, foldr, foldr1,
                        all, any, and, or, sum, product, maximum, minimum,
                        scanl, scanl1, scanr, scanr1,
                        enumFromTo, enumFromThenTo,
                        mapM, mapM_, sequence, sequence_,
                        showsPrec )

import qualified Text.Read as Read
import Data.Typeable ( Typeable1, gcast1 )

#include "../../include/vector.h"

import Data.Data ( Data, DataType )
--LIQUID #if MIN_VERSION_base(4,2,0)
import Data.Data ( mkNoRepType )
--LIQUID #else
--LIQUID import Data.Data ( mkNorepType )
--LIQUID mkNoRepType :: String -> DataType
--LIQUID mkNoRepType = mkNorepType
--LIQUID #endif

-- Length information
-- ------------------

-- | /O(1)/ Yield the length of the vector.
length :: Vector v a => v a -> Int
{-# INLINE_STREAM length #-}
length v = basicLength v

{-# RULES

"length/unstream [Vector]" forall s.
  length (new (New.unstream s)) = Stream.length s

  #-}

-- | /O(1)/ Test whether a vector if empty
null :: Vector v a => v a -> Bool
{-# INLINE_STREAM null #-}
null v = basicLength v == 0

{-# RULES

"null/unstream [Vector]" forall s.
  null (new (New.unstream s)) = Stream.null s

  #-}

-- Indexing
-- --------

infixl 9 !
-- | O(1) Indexing
(!) :: Vector v a => v a -> Int -> a
{-# INLINE_STREAM (!) #-}
(!) v i = BOUNDS_CHECK(checkIndex) "(!)" i (length v)
        $ unId (basicUnsafeIndexM v i)

infixl 9 !?
-- | O(1) Safe indexing
(!?) :: Vector v a => v a -> Int -> Maybe a
{-# INLINE_STREAM (!?) #-}
v !? i | i < 0 || i >= length v = Nothing
       | otherwise              = Just $ unsafeIndex v i

-- | /O(1)/ First element
head :: Vector v a => v a -> a
{-# INLINE_STREAM head #-}
head v = v ! 0

-- | /O(1)/ Last element
last :: Vector v a => v a -> a
{-# INLINE_STREAM last #-}
last v = v ! (length v - 1)

-- | /O(1)/ Unsafe indexing without bounds checking
unsafeIndex :: Vector v a => v a -> Int -> a
{-# INLINE_STREAM unsafeIndex #-}
unsafeIndex v i = UNSAFE_CHECK(checkIndex) "unsafeIndex" i (length v)
                $ unId (basicUnsafeIndexM v i)

-- | /O(1)/ First element without checking if the vector is empty
unsafeHead :: Vector v a => v a -> a
{-# INLINE_STREAM unsafeHead #-}
unsafeHead v = unsafeIndex v 0

-- | /O(1)/ Last element without checking if the vector is empty
unsafeLast :: Vector v a => v a -> a
{-# INLINE_STREAM unsafeLast #-}
unsafeLast v = unsafeIndex v (length v - 1)

{-# RULES

"(!)/unstream [Vector]" forall i s.
  new (New.unstream s) ! i = s Stream.!! i

"(!?)/unstream [Vector]" forall i s.
  new (New.unstream s) !? i = s Stream.!? i

"head/unstream [Vector]" forall s.
  head (new (New.unstream s)) = Stream.head s

"last/unstream [Vector]" forall s.
  last (new (New.unstream s)) = Stream.last s

"unsafeIndex/unstream [Vector]" forall i s.
  unsafeIndex (new (New.unstream s)) i = s Stream.!! i

"unsafeHead/unstream [Vector]" forall s.
  unsafeHead (new (New.unstream s)) = Stream.head s

"unsafeLast/unstream [Vector]" forall s.
  unsafeLast (new (New.unstream s)) = Stream.last s

 #-}

-- Monadic indexing
-- ----------------

-- | /O(1)/ Indexing in a monad.
--
-- The monad allows operations to be strict in the vector when necessary.
-- Suppose vector copying is implemented like this:
--
-- > copy mv v = ... write mv i (v ! i) ...
--
-- For lazy vectors, @v ! i@ would not be evaluated which means that @mv@
-- would unnecessarily retain a reference to @v@ in each element written.
--
-- With 'indexM', copying can be implemented like this instead:
--
-- > copy mv v = ... do
-- >                   x <- indexM v i
-- >                   write mv i x
--
-- Here, no references to @v@ are retained because indexing (but /not/ the
-- elements) is evaluated eagerly.
--
indexM :: (Vector v a, Monad m) => v a -> Int -> m a
{-# INLINE_STREAM indexM #-}
indexM v i = BOUNDS_CHECK(checkIndex) "indexM" i (length v)
           $ basicUnsafeIndexM v i

-- | /O(1)/ First element of a vector in a monad. See 'indexM' for an
-- explanation of why this is useful.
headM :: (Vector v a, Monad m) => v a -> m a
{-# INLINE_STREAM headM #-}
headM v = indexM v 0

-- | /O(1)/ Last element of a vector in a monad. See 'indexM' for an
-- explanation of why this is useful.
lastM :: (Vector v a, Monad m) => v a -> m a
{-# INLINE_STREAM lastM #-}
lastM v = indexM v (length v - 1)

-- | /O(1)/ Indexing in a monad without bounds checks. See 'indexM' for an
-- explanation of why this is useful.
unsafeIndexM :: (Vector v a, Monad m) => v a -> Int -> m a
{-# INLINE_STREAM unsafeIndexM #-}
unsafeIndexM v i = UNSAFE_CHECK(checkIndex) "unsafeIndexM" i (length v)
                 $ basicUnsafeIndexM v i

-- | /O(1)/ First element in a monad without checking for empty vectors.
-- See 'indexM' for an explanation of why this is useful.
unsafeHeadM :: (Vector v a, Monad m) => v a -> m a
{-# INLINE_STREAM unsafeHeadM #-}
unsafeHeadM v = unsafeIndexM v 0

-- | /O(1)/ Last element in a monad without checking for empty vectors.
-- See 'indexM' for an explanation of why this is useful.
unsafeLastM :: (Vector v a, Monad m) => v a -> m a
{-# INLINE_STREAM unsafeLastM #-}
unsafeLastM v = unsafeIndexM v (length v - 1)

{-# RULES

"indexM/unstream [Vector]" forall s i.
  indexM (new (New.unstream s)) i = liftStream s MStream.!! i

"headM/unstream [Vector]" forall s.
  headM (new (New.unstream s)) = MStream.head (liftStream s)

"lastM/unstream [Vector]" forall s.
  lastM (new (New.unstream s)) = MStream.last (liftStream s)

"unsafeIndexM/unstream [Vector]" forall s i.
  unsafeIndexM (new (New.unstream s)) i = liftStream s MStream.!! i

"unsafeHeadM/unstream [Vector]" forall s.
  unsafeHeadM (new (New.unstream s)) = MStream.head (liftStream s)

"unsafeLastM/unstream [Vector]" forall s.
  unsafeLastM (new (New.unstream s)) = MStream.last (liftStream s)

  #-}

-- Extracting subvectors (slicing)
-- -------------------------------

-- | /O(1)/ Yield a slice of the vector without copying it. The vector must
-- contain at least @i+n@ elements.
slice :: Vector v a => Int   -- ^ @i@ starting index
                    -> Int   -- ^ @n@ length
                    -> v a
                    -> v a
{-# INLINE_STREAM slice #-}
slice i n v = BOUNDS_CHECK(checkSlice) "slice" i n (length v)
            $ basicUnsafeSlice i n v

-- | /O(1)/ Yield all but the last element without copying. The vector may not
-- be empty.
init :: Vector v a => v a -> v a
{-# INLINE_STREAM init #-}
init v = slice 0 (length v - 1) v

-- | /O(1)/ Yield all but the first element without copying. The vector may not
-- be empty.
tail :: Vector v a => v a -> v a
{-# INLINE_STREAM tail #-}
tail v = slice 1 (length v - 1) v

-- | /O(1)/ Yield the first @n@ elements without copying. The vector may
-- contain less than @n@ elements in which case it is returned unchanged.
take :: Vector v a => Int -> v a -> v a
{-# INLINE_STREAM take #-}
take n v = unsafeSlice 0 (delay_inline min n' (length v)) v
  where n' = max n 0

-- | /O(1)/ Yield all but the first @n@ elements without copying. The vector may
-- contain less than @n@ elements in which case an empty vector is returned.
drop :: Vector v a => Int -> v a -> v a
{-# INLINE_STREAM drop #-}
drop n v = unsafeSlice (delay_inline min n' len)
                       (delay_inline max 0 (len - n')) v
  where n' = max n 0
        len = length v

-- | /O(1)/ Yield the first @n@ elements paired with the remainder without copying.
--
-- Note that @'splitAt' n v@ is equivalent to @('take' n v, 'drop' n v)@
-- but slightly more efficient.
{-# INLINE_STREAM splitAt #-}
splitAt :: Vector v a => Int -> v a -> (v a, v a)
splitAt n v = ( unsafeSlice 0 m v
              , unsafeSlice m (delay_inline max 0 (len - n')) v
              )
    where
      m   = delay_inline min n' len
      n'  = max n 0
      len = length v

-- | /O(1)/ Yield a slice of the vector without copying. The vector must
-- contain at least @i+n@ elements but this is not checked.
unsafeSlice :: Vector v a => Int   -- ^ @i@ starting index
                          -> Int   -- ^ @n@ length
                          -> v a
                          -> v a
{-# INLINE_STREAM unsafeSlice #-}
unsafeSlice i n v = UNSAFE_CHECK(checkSlice) "unsafeSlice" i n (length v)
                  $ basicUnsafeSlice i n v

-- | /O(1)/ Yield all but the last element without copying. The vector may not
-- be empty but this is not checked.
unsafeInit :: Vector v a => v a -> v a
{-# INLINE_STREAM unsafeInit #-}
unsafeInit v = unsafeSlice 0 (length v - 1) v

-- | /O(1)/ Yield all but the first element without copying. The vector may not
-- be empty but this is not checked.
unsafeTail :: Vector v a => v a -> v a
{-# INLINE_STREAM unsafeTail #-}
unsafeTail v = unsafeSlice 1 (length v - 1) v

-- | /O(1)/ Yield the first @n@ elements without copying. The vector must
-- contain at least @n@ elements but this is not checked.
unsafeTake :: Vector v a => Int -> v a -> v a
{-# INLINE unsafeTake #-}
unsafeTake n v = unsafeSlice 0 n v

-- | /O(1)/ Yield all but the first @n@ elements without copying. The vector
-- must contain at least @n@ elements but this is not checked.
unsafeDrop :: Vector v a => Int -> v a -> v a
{-# INLINE unsafeDrop #-}
unsafeDrop n v = unsafeSlice n (length v - n) v

{-# RULES

"slice/new [Vector]" forall i n p.
  slice i n (new p) = new (New.slice i n p)

"init/new [Vector]" forall p.
  init (new p) = new (New.init p)

"tail/new [Vector]" forall p.
  tail (new p) = new (New.tail p)

"take/new [Vector]" forall n p.
  take n (new p) = new (New.take n p)

"drop/new [Vector]" forall n p.
  drop n (new p) = new (New.drop n p)

"unsafeSlice/new [Vector]" forall i n p.
  unsafeSlice i n (new p) = new (New.unsafeSlice i n p)

"unsafeInit/new [Vector]" forall p.
  unsafeInit (new p) = new (New.unsafeInit p)

"unsafeTail/new [Vector]" forall p.
  unsafeTail (new p) = new (New.unsafeTail p)

  #-}

-- Initialisation
-- --------------

-- | /O(1)/ Empty vector
empty :: Vector v a => v a
{-# INLINE empty #-}
empty = unstream Stream.empty

-- | /O(1)/ Vector with exactly one element
singleton :: forall v a. Vector v a => a -> v a
{-# INLINE singleton #-}
singleton x = elemseq (undefined :: v a) x
            $ unstream (Stream.singleton x)

-- | /O(n)/ Vector of the given length with the same value in each position
replicate :: forall v a. Vector v a => Int -> a -> v a
{-# INLINE replicate #-}
replicate n x = elemseq (undefined :: v a) x
              $ unstream
              $ Stream.replicate n x

-- | /O(n)/ Construct a vector of the given length by applying the function to
-- each index
generate :: Vector v a => Int -> (Int -> a) -> v a
{-# INLINE generate #-}
generate n f = unstream (Stream.generate n f)

-- | /O(n)/ Apply function n times to value. Zeroth element is original value.
iterateN :: Vector v a => Int -> (a -> a) -> a -> v a
{-# INLINE iterateN #-}
iterateN n f x = unstream (Stream.iterateN n f x)

-- Unfolding
-- ---------

-- | /O(n)/ Construct a vector by repeatedly applying the generator function
-- to a seed. The generator function yields 'Just' the next element and the
-- new seed or 'Nothing' if there are no more elements.
--
-- > unfoldr (\n -> if n == 0 then Nothing else Just (n,n-1)) 10
-- >  = <10,9,8,7,6,5,4,3,2,1>
unfoldr :: Vector v a => (b -> Maybe (a, b)) -> b -> v a
{-# INLINE unfoldr #-}
unfoldr f = unstream . Stream.unfoldr f

-- | /O(n)/ Construct a vector with at most @n@ by repeatedly applying the
-- generator function to the a seed. The generator function yields 'Just' the
-- next element and the new seed or 'Nothing' if there are no more elements.
--
-- > unfoldrN 3 (\n -> Just (n,n-1)) 10 = <10,9,8>
unfoldrN  :: Vector v a => Int -> (b -> Maybe (a, b)) -> b -> v a
{-# INLINE unfoldrN #-}
unfoldrN n f = unstream . Stream.unfoldrN n f

-- | /O(n)/ Construct a vector with @n@ elements by repeatedly applying the
-- generator function to the already constructed part of the vector.
--
-- > constructN 3 f = let a = f <> ; b = f <a> ; c = f <a,b> in f <a,b,c>
--
constructN :: forall v a. Vector v a => Int -> (v a -> a) -> v a
{-# INLINE constructN #-}
-- NOTE: We *CANNOT* wrap this in New and then fuse because the elements
-- might contain references to the immutable vector!
constructN !n f = runST (
  do
    v  <- M.new n
    v' <- unsafeFreeze v
    fill v' 0
  )
  where
    fill :: forall s. v a -> Int -> ST s (v a)
    fill !v i | i < n = let x = f (unsafeTake i v)
                        in
                        elemseq v x $
                        do
                          v'  <- unsafeThaw v
                          M.unsafeWrite v' i x
                          v'' <- unsafeFreeze v'
                          fill v'' (i+1)

    fill v i = return v

-- | /O(n)/ Construct a vector with @n@ elements from right to left by
-- repeatedly applying the generator function to the already constructed part
-- of the vector.
--
-- > constructrN 3 f = let a = f <> ; b = f<a> ; c = f <b,a> in f <c,b,a>
--
constructrN :: forall v a. Vector v a => Int -> (v a -> a) -> v a
{-# INLINE constructrN #-}
-- NOTE: We *CANNOT* wrap this in New and then fuse because the elements
-- might contain references to the immutable vector!
constructrN !n f = runST (
  do
    v  <- n `seq` M.new n
    v' <- unsafeFreeze v
    fill v' 0
  )
  where
    fill :: forall s. v a -> Int -> ST s (v a)
    fill !v i | i < n = let x = f (unsafeSlice (n-i) i v)
                        in
                        elemseq v x $
                        do
                          v'  <- unsafeThaw v
                          M.unsafeWrite v' (n-i-1) x
                          v'' <- unsafeFreeze v'
                          fill v'' (i+1)

    fill v i = return v


-- Enumeration
-- -----------

-- | /O(n)/ Yield a vector of the given length containing the values @x@, @x+1@
-- etc. This operation is usually more efficient than 'enumFromTo'.
--
-- > enumFromN 5 3 = <5,6,7>
enumFromN :: (Vector v a, Num a) => a -> Int -> v a
{-# INLINE enumFromN #-}
enumFromN x n = enumFromStepN x 1 n

-- | /O(n)/ Yield a vector of the given length containing the values @x@, @x+y@,
-- @x+y+y@ etc. This operations is usually more efficient than 'enumFromThenTo'.
--
-- > enumFromStepN 1 0.1 5 = <1,1.1,1.2,1.3,1.4>
enumFromStepN :: forall v a. (Vector v a, Num a) => a -> a -> Int -> v a
{-# INLINE enumFromStepN #-}
enumFromStepN x y n = elemseq (undefined :: v a) x
                    $ elemseq (undefined :: v a) y
                    $ unstream
                    $ Stream.enumFromStepN  x y n

-- | /O(n)/ Enumerate values from @x@ to @y@.
--
-- /WARNING:/ This operation can be very inefficient. If at all possible, use
-- 'enumFromN' instead.
enumFromTo :: (Vector v a, Enum a) => a -> a -> v a
{-# INLINE enumFromTo #-}
enumFromTo x y = unstream (Stream.enumFromTo x y)

-- | /O(n)/ Enumerate values from @x@ to @y@ with a specific step @z@.
--
-- /WARNING:/ This operation can be very inefficient. If at all possible, use
-- 'enumFromStepN' instead.
enumFromThenTo :: (Vector v a, Enum a) => a -> a -> a -> v a
{-# INLINE enumFromThenTo #-}
enumFromThenTo x y z = unstream (Stream.enumFromThenTo x y z)

-- Concatenation
-- -------------

-- | /O(n)/ Prepend an element
cons :: forall v a. Vector v a => a -> v a -> v a
{-# INLINE cons #-}
cons x v = elemseq (undefined :: v a) x
         $ unstream
         $ Stream.cons x
         $ stream v

-- | /O(n)/ Append an element
snoc :: forall v a. Vector v a => v a -> a -> v a
{-# INLINE snoc #-}
snoc v x = elemseq (undefined :: v a) x
         $ unstream
         $ Stream.snoc (stream v) x

infixr 5 ++
-- | /O(m+n)/ Concatenate two vectors
(++) :: Vector v a => v a -> v a -> v a
{-# INLINE (++) #-}
v ++ w = unstream (stream v Stream.++ stream w)

-- | /O(n)/ Concatenate all vectors in the list
concat :: Vector v a => [v a] -> v a
{-# INLINE concat #-}
concat vs = unstream (Stream.flatten mk step (Exact n) (Stream.fromList vs))
  where
    n = List.foldl' (\k v -> k + length v) 0 vs

    {-# INLINE_INNER step #-}
    step (v,i,k)
      | i < k = case unsafeIndexM v i of
                  Box x -> Stream.Yield x (v,i+1,k)
      | otherwise = Stream.Done

    {-# INLINE mk #-}
    mk v = let k = length v
           in
           k `seq` (v,0,k)

-- Monadic initialisation
-- ----------------------

-- | /O(n)/ Execute the monadic action the given number of times and store the
-- results in a vector.
replicateM :: (Monad m, Vector v a) => Int -> m a -> m (v a)
{-# INLINE replicateM #-}
replicateM n m = unstreamM (MStream.replicateM n m)

-- | /O(n)/ Construct a vector of the given length by applying the monadic
-- action to each index
generateM :: (Monad m, Vector v a) => Int -> (Int -> m a) -> m (v a)
{-# INLINE generateM #-}
generateM n f = unstreamM (MStream.generateM n f)

-- | Execute the monadic action and freeze the resulting vector.
--
-- @
-- create (do { v \<- 'M.new' 2; 'M.write' v 0 \'a\'; 'M.write' v 1 \'b\'; return v }) = \<'a','b'\>
-- @
create :: Vector v a => (forall s. ST s (Mutable v s a)) -> v a
{-# INLINE create #-}
create p = new (New.create p)

-- Restricting memory usage
-- ------------------------

-- | /O(n)/ Yield the argument but force it not to retain any extra memory,
-- possibly by copying it.
--
-- This is especially useful when dealing with slices. For example:
--
-- > force (slice 0 2 <huge vector>)
--
-- Here, the slice retains a reference to the huge vector. Forcing it creates
-- a copy of just the elements that belong to the slice and allows the huge
-- vector to be garbage collected.
force :: Vector v a => v a -> v a
-- FIXME: we probably ought to inline this later as the rules still might fire
-- otherwise
{-# INLINE_STREAM force #-}
force v = new (clone v)

-- Bulk updates
-- ------------

-- | /O(m+n)/ For each pair @(i,a)@ from the list, replace the vector
-- element at position @i@ by @a@.
--
-- > <5,9,2,7> // [(2,1),(0,3),(2,8)] = <3,9,8,7>
--
(//) :: Vector v a => v a        -- ^ initial vector (of length @m@)
                   -> [(Int, a)] -- ^ list of index/value pairs (of length @n@)
                   -> v a
{-# INLINE (//) #-}
v // us = update_stream v (Stream.fromList us)

-- | /O(m+n)/ For each pair @(i,a)@ from the vector of index/value pairs,
-- replace the vector element at position @i@ by @a@.
--
-- > update <5,9,2,7> <(2,1),(0,3),(2,8)> = <3,9,8,7>
--
update :: (Vector v a, Vector v (Int, a))
        => v a        -- ^ initial vector (of length @m@)
        -> v (Int, a) -- ^ vector of index/value pairs (of length @n@)
        -> v a
{-# INLINE update #-}
update v w = update_stream v (stream w)

-- | /O(m+min(n1,n2))/ For each index @i@ from the index vector and the
-- corresponding value @a@ from the value vector, replace the element of the
-- initial vector at position @i@ by @a@.
--
-- > update_ <5,9,2,7>  <2,0,2> <1,3,8> = <3,9,8,7>
--
-- This function is useful for instances of 'Vector' that cannot store pairs.
-- Otherwise, 'update' is probably more convenient.
--
-- @
-- update_ xs is ys = 'update' xs ('zip' is ys)
-- @
update_ :: (Vector v a, Vector v Int)
        => v a   -- ^ initial vector (of length @m@)
        -> v Int -- ^ index vector (of length @n1@)
        -> v a   -- ^ value vector (of length @n2@)
        -> v a
{-# INLINE update_ #-}
update_ v is w = update_stream v (Stream.zipWith (,) (stream is) (stream w))

update_stream :: Vector v a => v a -> Stream (Int,a) -> v a
{-# INLINE update_stream #-}
update_stream = modifyWithStream M.update

-- | Same as ('//') but without bounds checking.
unsafeUpd :: Vector v a => v a -> [(Int, a)] -> v a
{-# INLINE unsafeUpd #-}
unsafeUpd v us = unsafeUpdate_stream v (Stream.fromList us)

-- | Same as 'update' but without bounds checking.
unsafeUpdate :: (Vector v a, Vector v (Int, a)) => v a -> v (Int, a) -> v a
{-# INLINE unsafeUpdate #-}
unsafeUpdate v w = unsafeUpdate_stream v (stream w)

-- | Same as 'update_' but without bounds checking.
unsafeUpdate_ :: (Vector v a, Vector v Int) => v a -> v Int -> v a -> v a
{-# INLINE unsafeUpdate_ #-}
unsafeUpdate_ v is w
  = unsafeUpdate_stream v (Stream.zipWith (,) (stream is) (stream w))

unsafeUpdate_stream :: Vector v a => v a -> Stream (Int,a) -> v a
{-# INLINE unsafeUpdate_stream #-}
unsafeUpdate_stream = modifyWithStream M.unsafeUpdate

-- Accumulations
-- -------------

-- | /O(m+n)/ For each pair @(i,b)@ from the list, replace the vector element
-- @a@ at position @i@ by @f a b@.
--
-- > accum (+) <5,9,2> [(2,4),(1,6),(0,3),(1,7)] = <5+3, 9+6+7, 2+4>
accum :: Vector v a
      => (a -> b -> a) -- ^ accumulating function @f@
      -> v a           -- ^ initial vector (of length @m@)
      -> [(Int,b)]     -- ^ list of index/value pairs (of length @n@)
      -> v a
{-# INLINE accum #-}
accum f v us = accum_stream f v (Stream.fromList us)

-- | /O(m+n)/ For each pair @(i,b)@ from the vector of pairs, replace the vector
-- element @a@ at position @i@ by @f a b@.
--
-- > accumulate (+) <5,9,2> <(2,4),(1,6),(0,3),(1,7)> = <5+3, 9+6+7, 2+4>
accumulate :: (Vector v a, Vector v (Int, b))
           => (a -> b -> a) -- ^ accumulating function @f@
           -> v a           -- ^ initial vector (of length @m@)
           -> v (Int,b)     -- ^ vector of index/value pairs (of length @n@)
           -> v a
{-# INLINE accumulate #-}
accumulate f v us = accum_stream f v (stream us)

-- | /O(m+min(n1,n2))/ For each index @i@ from the index vector and the
-- corresponding value @b@ from the the value vector,
-- replace the element of the initial vector at
-- position @i@ by @f a b@.
--
-- > accumulate_ (+) <5,9,2> <2,1,0,1> <4,6,3,7> = <5+3, 9+6+7, 2+4>
--
-- This function is useful for instances of 'Vector' that cannot store pairs.
-- Otherwise, 'accumulate' is probably more convenient:
--
-- @
-- accumulate_ f as is bs = 'accumulate' f as ('zip' is bs)
-- @
accumulate_ :: (Vector v a, Vector v Int, Vector v b)
                => (a -> b -> a) -- ^ accumulating function @f@
                -> v a           -- ^ initial vector (of length @m@)
                -> v Int         -- ^ index vector (of length @n1@)
                -> v b           -- ^ value vector (of length @n2@)
                -> v a
{-# INLINE accumulate_ #-}
accumulate_ f v is xs = accum_stream f v (Stream.zipWith (,) (stream is)
                                                             (stream xs))
                                        

accum_stream :: Vector v a => (a -> b -> a) -> v a -> Stream (Int,b) -> v a
{-# INLINE accum_stream #-}
accum_stream f = modifyWithStream (M.accum f)

-- | Same as 'accum' but without bounds checking.
unsafeAccum :: Vector v a => (a -> b -> a) -> v a -> [(Int,b)] -> v a
{-# INLINE unsafeAccum #-}
unsafeAccum f v us = unsafeAccum_stream f v (Stream.fromList us)

-- | Same as 'accumulate' but without bounds checking.
unsafeAccumulate :: (Vector v a, Vector v (Int, b))
                => (a -> b -> a) -> v a -> v (Int,b) -> v a
{-# INLINE unsafeAccumulate #-}
unsafeAccumulate f v us = unsafeAccum_stream f v (stream us)

-- | Same as 'accumulate_' but without bounds checking.
unsafeAccumulate_ :: (Vector v a, Vector v Int, Vector v b)
                => (a -> b -> a) -> v a -> v Int -> v b -> v a
{-# INLINE unsafeAccumulate_ #-}
unsafeAccumulate_ f v is xs
  = unsafeAccum_stream f v (Stream.zipWith (,) (stream is) (stream xs))

unsafeAccum_stream
  :: Vector v a => (a -> b -> a) -> v a -> Stream (Int,b) -> v a
{-# INLINE unsafeAccum_stream #-}
unsafeAccum_stream f = modifyWithStream (M.unsafeAccum f)

-- Permutations
-- ------------

-- | /O(n)/ Reverse a vector
reverse :: (Vector v a) => v a -> v a
{-# INLINE reverse #-}
-- FIXME: make this fuse better, add support for recycling
reverse = unstream . streamR

-- | /O(n)/ Yield the vector obtained by replacing each element @i@ of the
-- index vector by @xs'!'i@. This is equivalent to @'map' (xs'!') is@ but is
-- often much more efficient.
--
-- > backpermute <a,b,c,d> <0,3,2,3,1,0> = <a,d,c,d,b,a>
backpermute :: (Vector v a, Vector v Int)
            => v a   -- ^ @xs@ value vector
            -> v Int -- ^ @is@ index vector (of length @n@)
            -> v a
{-# INLINE backpermute #-}
-- This somewhat non-intuitive definition ensures that the resulting vector
-- does not retain references to the original one even if it is lazy in its
-- elements. This would not be the case if we simply used map (v!)
backpermute v is = seq v
                 $ seq n
                 $ unstream
                 $ Stream.unbox
                 $ Stream.map index
                 $ stream is
  where
    n = length v

    {-# INLINE index #-}
    -- NOTE: we do it this way to avoid triggering LiberateCase on n in
    -- polymorphic code
    index i = BOUNDS_CHECK(checkIndex) "backpermute" i n
            $ basicUnsafeIndexM v i

-- | Same as 'backpermute' but without bounds checking.
unsafeBackpermute :: (Vector v a, Vector v Int) => v a -> v Int -> v a
{-# INLINE unsafeBackpermute #-}
unsafeBackpermute v is = seq v
                       $ seq n
                       $ unstream
                       $ Stream.unbox
                       $ Stream.map index
                       $ stream is
  where
    n = length v

    {-# INLINE index #-}
    -- NOTE: we do it this way to avoid triggering LiberateCase on n in
    -- polymorphic code
    index i = UNSAFE_CHECK(checkIndex) "unsafeBackpermute" i n
            $ basicUnsafeIndexM v i

-- Safe destructive updates
-- ------------------------

-- | Apply a destructive operation to a vector. The operation will be
-- performed in place if it is safe to do so and will modify a copy of the
-- vector otherwise.
--
-- @
-- modify (\\v -> 'M.write' v 0 \'x\') ('replicate' 3 \'a\') = \<\'x\',\'a\',\'a\'\>
-- @
modify :: Vector v a => (forall s. Mutable v s a -> ST s ()) -> v a -> v a
{-# INLINE modify #-}
modify p = new . New.modify p . clone

-- We have to make sure that this is strict in the stream but we can't seq on
-- it while fusion is happening. Hence this ugliness.
modifyWithStream :: Vector v a
                 => (forall s. Mutable v s a -> Stream b -> ST s ())
                 -> v a -> Stream b -> v a
{-# INLINE modifyWithStream #-}
modifyWithStream p v s = new (New.modifyWithStream p (clone v) s)

-- Indexing
-- --------

-- | /O(n)/ Pair each element in a vector with its index
indexed :: (Vector v a, Vector v (Int,a)) => v a -> v (Int,a)
{-# INLINE indexed #-}
indexed = unstream . Stream.indexed . stream

-- Mapping
-- -------

-- | /O(n)/ Map a function over a vector
map :: (Vector v a, Vector v b) => (a -> b) -> v a -> v b
{-# INLINE map #-}
map f = unstream . inplace (MStream.map f) . stream

-- | /O(n)/ Apply a function to every element of a vector and its index
imap :: (Vector v a, Vector v b) => (Int -> a -> b) -> v a -> v b
{-# INLINE imap #-}
imap f = unstream . inplace (MStream.map (uncurry f) . MStream.indexed)
                  . stream

-- | Map a function over a vector and concatenate the results.
concatMap :: (Vector v a, Vector v b) => (a -> v b) -> v a -> v b
{-# INLINE concatMap #-}
-- NOTE: We can't fuse concatMap anyway so don't pretend we do.
-- This seems to be slightly slower
-- concatMap f = concat . Stream.toList . Stream.map f . stream

-- Slowest
-- concatMap f = unstream . Stream.concatMap (stream . f) . stream

-- Seems to be fastest
concatMap f = unstream
            . Stream.flatten mk step Unknown
            . stream
  where
    {-# INLINE_INNER step #-}
    step (v,i,k)
      | i < k = case unsafeIndexM v i of
                  Box x -> Stream.Yield x (v,i+1,k)
      | otherwise = Stream.Done

    {-# INLINE mk #-}
    mk x = let v = f x
               k = length v
           in
           k `seq` (v,0,k)

-- Monadic mapping
-- ---------------

-- | /O(n)/ Apply the monadic action to all elements of the vector, yielding a
-- vector of results
mapM :: (Monad m, Vector v a, Vector v b) => (a -> m b) -> v a -> m (v b)
{-# INLINE mapM #-}
mapM f = unstreamM . Stream.mapM f . stream

-- | /O(n)/ Apply the monadic action to all elements of a vector and ignore the
-- results
mapM_ :: (Monad m, Vector v a) => (a -> m b) -> v a -> m ()
{-# INLINE mapM_ #-}
mapM_ f = Stream.mapM_ f . stream

-- | /O(n)/ Apply the monadic action to all elements of the vector, yielding a
-- vector of results. Equvalent to @flip 'mapM'@.
forM :: (Monad m, Vector v a, Vector v b) => v a -> (a -> m b) -> m (v b)
{-# INLINE forM #-}
forM as f = mapM f as

-- | /O(n)/ Apply the monadic action to all elements of a vector and ignore the
-- results. Equivalent to @flip 'mapM_'@.
forM_ :: (Monad m, Vector v a) => v a -> (a -> m b) -> m ()
{-# INLINE forM_ #-}
forM_ as f = mapM_ f as

-- Zipping
-- -------

-- | /O(min(m,n))/ Zip two vectors with the given function.
zipWith :: (Vector v a, Vector v b, Vector v c)
        => (a -> b -> c) -> v a -> v b -> v c
{-# INLINE zipWith #-}
zipWith f xs ys = unstream (Stream.zipWith f (stream xs) (stream ys))

-- | Zip three vectors with the given function.
zipWith3 :: (Vector v a, Vector v b, Vector v c, Vector v d)
         => (a -> b -> c -> d) -> v a -> v b -> v c -> v d
{-# INLINE zipWith3 #-}
zipWith3 f as bs cs = unstream (Stream.zipWith3 f (stream as)
                                                  (stream bs)
                                                  (stream cs))

zipWith4 :: (Vector v a, Vector v b, Vector v c, Vector v d, Vector v e)
         => (a -> b -> c -> d -> e) -> v a -> v b -> v c -> v d -> v e
{-# INLINE zipWith4 #-}
zipWith4 f as bs cs ds
  = unstream (Stream.zipWith4 f (stream as)
                                (stream bs)
                                (stream cs)
                                (stream ds))

zipWith5 :: (Vector v a, Vector v b, Vector v c, Vector v d, Vector v e,
             Vector v f)
         => (a -> b -> c -> d -> e -> f) -> v a -> v b -> v c -> v d -> v e
                                         -> v f
{-# INLINE zipWith5 #-}
zipWith5 f as bs cs ds es
  = unstream (Stream.zipWith5 f (stream as)
                                (stream bs)
                                (stream cs)
                                (stream ds)
                                (stream es))

zipWith6 :: (Vector v a, Vector v b, Vector v c, Vector v d, Vector v e,
             Vector v f, Vector v g)
         => (a -> b -> c -> d -> e -> f -> g)
         -> v a -> v b -> v c -> v d -> v e -> v f -> v g
{-# INLINE zipWith6 #-}
zipWith6 f as bs cs ds es fs
  = unstream (Stream.zipWith6 f (stream as)
                                (stream bs)
                                (stream cs)
                                (stream ds)
                                (stream es)
                                (stream fs))

-- | /O(min(m,n))/ Zip two vectors with a function that also takes the
-- elements' indices.
izipWith :: (Vector v a, Vector v b, Vector v c)
        => (Int -> a -> b -> c) -> v a -> v b -> v c
{-# INLINE izipWith #-}
izipWith f xs ys = unstream
                  (Stream.zipWith (uncurry f) (Stream.indexed (stream xs))
                                                              (stream ys))

izipWith3 :: (Vector v a, Vector v b, Vector v c, Vector v d)
         => (Int -> a -> b -> c -> d) -> v a -> v b -> v c -> v d
{-# INLINE izipWith3 #-}
izipWith3 f as bs cs
  = unstream (Stream.zipWith3 (uncurry f) (Stream.indexed (stream as))
                                                          (stream bs)
                                                          (stream cs))

izipWith4 :: (Vector v a, Vector v b, Vector v c, Vector v d, Vector v e)
         => (Int -> a -> b -> c -> d -> e) -> v a -> v b -> v c -> v d -> v e
{-# INLINE izipWith4 #-}
izipWith4 f as bs cs ds
  = unstream (Stream.zipWith4 (uncurry f) (Stream.indexed (stream as))
                                                          (stream bs)
                                                          (stream cs)
                                                          (stream ds))

izipWith5 :: (Vector v a, Vector v b, Vector v c, Vector v d, Vector v e,
             Vector v f)
         => (Int -> a -> b -> c -> d -> e -> f) -> v a -> v b -> v c -> v d
                                                -> v e -> v f
{-# INLINE izipWith5 #-}
izipWith5 f as bs cs ds es
  = unstream (Stream.zipWith5 (uncurry f) (Stream.indexed (stream as))
                                                          (stream bs)
                                                          (stream cs)
                                                          (stream ds)
                                                          (stream es))

izipWith6 :: (Vector v a, Vector v b, Vector v c, Vector v d, Vector v e,
             Vector v f, Vector v g)
         => (Int -> a -> b -> c -> d -> e -> f -> g)
         -> v a -> v b -> v c -> v d -> v e -> v f -> v g
{-# INLINE izipWith6 #-}
izipWith6 f as bs cs ds es fs
  = unstream (Stream.zipWith6 (uncurry f) (Stream.indexed (stream as))
                                                          (stream bs)
                                                          (stream cs)
                                                          (stream ds)
                                                          (stream es)
                                                          (stream fs))

-- | /O(min(m,n))/ Zip two vectors
zip :: (Vector v a, Vector v b, Vector v (a,b)) => v a -> v b -> v (a, b)
{-# INLINE zip #-}
zip = zipWith (,)

zip3 :: (Vector v a, Vector v b, Vector v c, Vector v (a, b, c))
     => v a -> v b -> v c -> v (a, b, c)
{-# INLINE zip3 #-}
zip3 = zipWith3 (,,)

zip4 :: (Vector v a, Vector v b, Vector v c, Vector v d, Vector v (a, b, c, d))
     => v a -> v b -> v c -> v d -> v (a, b, c, d)
{-# INLINE zip4 #-}
zip4 = zipWith4 (,,,)

zip5 :: (Vector v a, Vector v b, Vector v c, Vector v d, Vector v e,
         Vector v (a, b, c, d, e))
     => v a -> v b -> v c -> v d -> v e -> v (a, b, c, d, e)
{-# INLINE zip5 #-}
zip5 = zipWith5 (,,,,)

zip6 :: (Vector v a, Vector v b, Vector v c, Vector v d, Vector v e,
         Vector v f, Vector v (a, b, c, d, e, f))
     => v a -> v b -> v c -> v d -> v e -> v f -> v (a, b, c, d, e, f)
{-# INLINE zip6 #-}
zip6 = zipWith6 (,,,,,)

-- Monadic zipping
-- ---------------

-- | /O(min(m,n))/ Zip the two vectors with the monadic action and yield a
-- vector of results
zipWithM :: (Monad m, Vector v a, Vector v b, Vector v c)
         => (a -> b -> m c) -> v a -> v b -> m (v c)
-- FIXME: specialise for ST and IO?
{-# INLINE zipWithM #-}
zipWithM f as bs = unstreamM $ Stream.zipWithM f (stream as) (stream bs)

-- | /O(min(m,n))/ Zip the two vectors with the monadic action and ignore the
-- results
zipWithM_ :: (Monad m, Vector v a, Vector v b)
          => (a -> b -> m c) -> v a -> v b -> m ()
{-# INLINE zipWithM_ #-}
zipWithM_ f as bs = Stream.zipWithM_ f (stream as) (stream bs)

-- Unzipping
-- ---------

-- | /O(min(m,n))/ Unzip a vector of pairs.
unzip :: (Vector v a, Vector v b, Vector v (a,b)) => v (a, b) -> (v a, v b)
{-# INLINE unzip #-}
unzip xs = (map fst xs, map snd xs)

unzip3 :: (Vector v a, Vector v b, Vector v c, Vector v (a, b, c))
       => v (a, b, c) -> (v a, v b, v c)
{-# INLINE unzip3 #-}
unzip3 xs = (map (\(a, b, c) -> a) xs,
             map (\(a, b, c) -> b) xs,
             map (\(a, b, c) -> c) xs)

unzip4 :: (Vector v a, Vector v b, Vector v c, Vector v d,
           Vector v (a, b, c, d))
       => v (a, b, c, d) -> (v a, v b, v c, v d)
{-# INLINE unzip4 #-}
unzip4 xs = (map (\(a, b, c, d) -> a) xs,
             map (\(a, b, c, d) -> b) xs,
             map (\(a, b, c, d) -> c) xs,
             map (\(a, b, c, d) -> d) xs)

unzip5 :: (Vector v a, Vector v b, Vector v c, Vector v d, Vector v e,
           Vector v (a, b, c, d, e))
       => v (a, b, c, d, e) -> (v a, v b, v c, v d, v e)
{-# INLINE unzip5 #-}
unzip5 xs = (map (\(a, b, c, d, e) -> a) xs,
             map (\(a, b, c, d, e) -> b) xs,
             map (\(a, b, c, d, e) -> c) xs,
             map (\(a, b, c, d, e) -> d) xs,
             map (\(a, b, c, d, e) -> e) xs)

unzip6 :: (Vector v a, Vector v b, Vector v c, Vector v d, Vector v e,
           Vector v f, Vector v (a, b, c, d, e, f))
       => v (a, b, c, d, e, f) -> (v a, v b, v c, v d, v e, v f)
{-# INLINE unzip6 #-}
unzip6 xs = (map (\(a, b, c, d, e, f) -> a) xs,
             map (\(a, b, c, d, e, f) -> b) xs,
             map (\(a, b, c, d, e, f) -> c) xs,
             map (\(a, b, c, d, e, f) -> d) xs,
             map (\(a, b, c, d, e, f) -> e) xs,
             map (\(a, b, c, d, e, f) -> f) xs)

-- Filtering
-- ---------

-- | /O(n)/ Drop elements that do not satisfy the predicate
filter :: Vector v a => (a -> Bool) -> v a -> v a
{-# INLINE filter #-}
filter f = unstream . inplace (MStream.filter f) . stream

-- | /O(n)/ Drop elements that do not satisfy the predicate which is applied to
-- values and their indices
ifilter :: Vector v a => (Int -> a -> Bool) -> v a -> v a
{-# INLINE ifilter #-}
ifilter f = unstream
          . inplace (MStream.map snd . MStream.filter (uncurry f)
                                     . MStream.indexed)
          . stream

-- | /O(n)/ Drop elements that do not satisfy the monadic predicate
filterM :: (Monad m, Vector v a) => (a -> m Bool) -> v a -> m (v a)
{-# INLINE filterM #-}
filterM f = unstreamM . Stream.filterM f . stream

-- | /O(n)/ Yield the longest prefix of elements satisfying the predicate
-- without copying.
takeWhile :: Vector v a => (a -> Bool) -> v a -> v a
{-# INLINE takeWhile #-}
takeWhile f = unstream . Stream.takeWhile f . stream

-- | /O(n)/ Drop the longest prefix of elements that satisfy the predicate
-- without copying.
dropWhile :: Vector v a => (a -> Bool) -> v a -> v a
{-# INLINE dropWhile #-}
dropWhile f = unstream . Stream.dropWhile f . stream

-- Parititioning
-- -------------

-- | /O(n)/ Split the vector in two parts, the first one containing those
-- elements that satisfy the predicate and the second one those that don't. The
-- relative order of the elements is preserved at the cost of a sometimes
-- reduced performance compared to 'unstablePartition'.
partition :: Vector v a => (a -> Bool) -> v a -> (v a, v a)
{-# INLINE partition #-}
partition f = partition_stream f . stream

-- FIXME: Make this inplace-fusible (look at how stable_partition is
-- implemented in C++)

partition_stream :: Vector v a => (a -> Bool) -> Stream a -> (v a, v a)
{-# INLINE_STREAM partition_stream #-}
partition_stream f s = s `seq` runST (
  do
    (mv1,mv2) <- M.partitionStream f s
    v1 <- unsafeFreeze mv1
    v2 <- unsafeFreeze mv2
    return (v1,v2))

-- | /O(n)/ Split the vector in two parts, the first one containing those
-- elements that satisfy the predicate and the second one those that don't.
-- The order of the elements is not preserved but the operation is often
-- faster than 'partition'.
unstablePartition :: Vector v a => (a -> Bool) -> v a -> (v a, v a)
{-# INLINE unstablePartition #-}
unstablePartition f = unstablePartition_stream f . stream

unstablePartition_stream
  :: Vector v a => (a -> Bool) -> Stream a -> (v a, v a)
{-# INLINE_STREAM unstablePartition_stream #-}
unstablePartition_stream f s = s `seq` runST (
  do
    (mv1,mv2) <- M.unstablePartitionStream f s
    v1 <- unsafeFreeze mv1
    v2 <- unsafeFreeze mv2
    return (v1,v2))

unstablePartition_new :: Vector v a => (a -> Bool) -> New v a -> (v a, v a)
{-# INLINE_STREAM unstablePartition_new #-}
unstablePartition_new f (New.New p) = runST (
  do
    mv <- p
    i <- M.unstablePartition f mv
    v <- unsafeFreeze mv
    return (unsafeTake i v, unsafeDrop i v))

{-# RULES

"unstablePartition" forall f p.
  unstablePartition_stream f (stream (new p))
    = unstablePartition_new f p

  #-}


-- FIXME: make span and break fusible

-- | /O(n)/ Split the vector into the longest prefix of elements that satisfy
-- the predicate and the rest without copying.
span :: Vector v a => (a -> Bool) -> v a -> (v a, v a)
{-# INLINE span #-}
span f = break (not . f)

-- | /O(n)/ Split the vector into the longest prefix of elements that do not
-- satisfy the predicate and the rest without copying.
break :: Vector v a => (a -> Bool) -> v a -> (v a, v a)
{-# INLINE break #-}
break f xs = case findIndex f xs of
               Just i  -> (unsafeSlice 0 i xs, unsafeSlice i (length xs - i) xs)
               Nothing -> (xs, empty)
    

-- Searching
-- ---------

infix 4 `elem`
-- | /O(n)/ Check if the vector contains an element
elem :: (Vector v a, Eq a) => a -> v a -> Bool
{-# INLINE elem #-}
elem x = Stream.elem x . stream

infix 4 `notElem`
-- | /O(n)/ Check if the vector does not contain an element (inverse of 'elem')
notElem :: (Vector v a, Eq a) => a -> v a -> Bool
{-# INLINE notElem #-}
notElem x = Stream.notElem x . stream

-- | /O(n)/ Yield 'Just' the first element matching the predicate or 'Nothing'
-- if no such element exists.
find :: Vector v a => (a -> Bool) -> v a -> Maybe a
{-# INLINE find #-}
find f = Stream.find f . stream

-- | /O(n)/ Yield 'Just' the index of the first element matching the predicate
-- or 'Nothing' if no such element exists.
findIndex :: Vector v a => (a -> Bool) -> v a -> Maybe Int
{-# INLINE findIndex #-}
findIndex f = Stream.findIndex f . stream

-- | /O(n)/ Yield the indices of elements satisfying the predicate in ascending
-- order.
findIndices :: (Vector v a, Vector v Int) => (a -> Bool) -> v a -> v Int
{-# INLINE findIndices #-}
findIndices f = unstream
              . inplace (MStream.map fst . MStream.filter (f . snd)
                                         . MStream.indexed)
              . stream

-- | /O(n)/ Yield 'Just' the index of the first occurence of the given element or
-- 'Nothing' if the vector does not contain the element. This is a specialised
-- version of 'findIndex'.
elemIndex :: (Vector v a, Eq a) => a -> v a -> Maybe Int
{-# INLINE elemIndex #-}
elemIndex x = findIndex (x==)

-- | /O(n)/ Yield the indices of all occurences of the given element in
-- ascending order. This is a specialised version of 'findIndices'.
elemIndices :: (Vector v a, Vector v Int, Eq a) => a -> v a -> v Int
{-# INLINE elemIndices #-}
elemIndices x = findIndices (x==)

-- Folding
-- -------

-- | /O(n)/ Left fold
foldl :: Vector v b => (a -> b -> a) -> a -> v b -> a
{-# INLINE foldl #-}
foldl f z = Stream.foldl f z . stream

-- | /O(n)/ Left fold on non-empty vectors
foldl1 :: Vector v a => (a -> a -> a) -> v a -> a
{-# INLINE foldl1 #-}
foldl1 f = Stream.foldl1 f . stream

-- | /O(n)/ Left fold with strict accumulator
foldl' :: Vector v b => (a -> b -> a) -> a -> v b -> a
{-# INLINE foldl' #-}
foldl' f z = Stream.foldl' f z . stream

-- | /O(n)/ Left fold on non-empty vectors with strict accumulator
foldl1' :: Vector v a => (a -> a -> a) -> v a -> a
{-# INLINE foldl1' #-}
foldl1' f = Stream.foldl1' f . stream

-- | /O(n)/ Right fold
foldr :: Vector v a => (a -> b -> b) -> b -> v a -> b
{-# INLINE foldr #-}
foldr f z = Stream.foldr f z . stream

-- | /O(n)/ Right fold on non-empty vectors
foldr1 :: Vector v a => (a -> a -> a) -> v a -> a
{-# INLINE foldr1 #-}
foldr1 f = Stream.foldr1 f . stream

-- | /O(n)/ Right fold with a strict accumulator
foldr' :: Vector v a => (a -> b -> b) -> b -> v a -> b
{-# INLINE foldr' #-}
foldr' f z = Stream.foldl' (flip f) z . streamR

-- | /O(n)/ Right fold on non-empty vectors with strict accumulator
foldr1' :: Vector v a => (a -> a -> a) -> v a -> a
{-# INLINE foldr1' #-}
foldr1' f = Stream.foldl1' (flip f) . streamR

-- | /O(n)/ Left fold (function applied to each element and its index)
ifoldl :: Vector v b => (a -> Int -> b -> a) -> a -> v b -> a
{-# INLINE ifoldl #-}
ifoldl f z = Stream.foldl (uncurry . f) z . Stream.indexed . stream

-- | /O(n)/ Left fold with strict accumulator (function applied to each element
-- and its index)
ifoldl' :: Vector v b => (a -> Int -> b -> a) -> a -> v b -> a
{-# INLINE ifoldl' #-}
ifoldl' f z = Stream.foldl' (uncurry . f) z . Stream.indexed . stream

-- | /O(n)/ Right fold (function applied to each element and its index)
ifoldr :: Vector v a => (Int -> a -> b -> b) -> b -> v a -> b
{-# INLINE ifoldr #-}
ifoldr f z = Stream.foldr (uncurry f) z . Stream.indexed . stream

-- | /O(n)/ Right fold with strict accumulator (function applied to each
-- element and its index)
ifoldr' :: Vector v a => (Int -> a -> b -> b) -> b -> v a -> b
{-# INLINE ifoldr' #-}
ifoldr' f z xs = Stream.foldl' (flip (uncurry f)) z
               $ Stream.indexedR (length xs) $ streamR xs

-- Specialised folds
-- -----------------

-- | /O(n)/ Check if all elements satisfy the predicate.
all :: Vector v a => (a -> Bool) -> v a -> Bool
{-# INLINE all #-}
all f = Stream.and . Stream.map f . stream

-- | /O(n)/ Check if any element satisfies the predicate.
any :: Vector v a => (a -> Bool) -> v a -> Bool
{-# INLINE any #-}
any f = Stream.or . Stream.map f . stream

-- | /O(n)/ Check if all elements are 'True'
and :: Vector v Bool => v Bool -> Bool
{-# INLINE and #-}
and = Stream.and . stream

-- | /O(n)/ Check if any element is 'True'
or :: Vector v Bool => v Bool -> Bool
{-# INLINE or #-}
or = Stream.or . stream

-- | /O(n)/ Compute the sum of the elements
sum :: (Vector v a, Num a) => v a -> a
{-# INLINE sum #-}
sum = Stream.foldl' (+) 0 . stream

-- | /O(n)/ Compute the produce of the elements
product :: (Vector v a, Num a) => v a -> a
{-# INLINE product #-}
product = Stream.foldl' (*) 1 . stream

-- | /O(n)/ Yield the maximum element of the vector. The vector may not be
-- empty.
maximum :: (Vector v a, Ord a) => v a -> a
{-# INLINE maximum #-}
maximum = Stream.foldl1' max . stream

-- | /O(n)/ Yield the maximum element of the vector according to the given
-- comparison function. The vector may not be empty.
maximumBy :: Vector v a => (a -> a -> Ordering) -> v a -> a
{-# INLINE maximumBy #-}
maximumBy cmp = Stream.foldl1' maxBy . stream
  where
    {-# INLINE maxBy #-}
    maxBy x y = case cmp x y of
                  LT -> y
                  _  -> x

-- | /O(n)/ Yield the minimum element of the vector. The vector may not be
-- empty.
minimum :: (Vector v a, Ord a) => v a -> a
{-# INLINE minimum #-}
minimum = Stream.foldl1' min . stream

-- | /O(n)/ Yield the minimum element of the vector according to the given
-- comparison function. The vector may not be empty.
minimumBy :: Vector v a => (a -> a -> Ordering) -> v a -> a
{-# INLINE minimumBy #-}
minimumBy cmp = Stream.foldl1' minBy . stream
  where
    {-# INLINE minBy #-}
    minBy x y = case cmp x y of
                  GT -> y
                  _  -> x

-- | /O(n)/ Yield the index of the maximum element of the vector. The vector
-- may not be empty.
maxIndex :: (Vector v a, Ord a) => v a -> Int
{-# INLINE maxIndex #-}
maxIndex = maxIndexBy compare

-- | /O(n)/ Yield the index of the maximum element of the vector according to
-- the given comparison function. The vector may not be empty.
maxIndexBy :: Vector v a => (a -> a -> Ordering) -> v a -> Int
{-# INLINE maxIndexBy #-}
maxIndexBy cmp = fst . Stream.foldl1' imax . Stream.indexed . stream
  where
    imax (i,x) (j,y) = i `seq` j `seq`
                       case cmp x y of
                         LT -> (j,y)
                         _  -> (i,x)

-- | /O(n)/ Yield the index of the minimum element of the vector. The vector
-- may not be empty.
minIndex :: (Vector v a, Ord a) => v a -> Int
{-# INLINE minIndex #-}
minIndex = minIndexBy compare

-- | /O(n)/ Yield the index of the minimum element of the vector according to
-- the given comparison function. The vector may not be empty.
minIndexBy :: Vector v a => (a -> a -> Ordering) -> v a -> Int
{-# INLINE minIndexBy #-}
minIndexBy cmp = fst . Stream.foldl1' imin . Stream.indexed . stream
  where
    imin (i,x) (j,y) = i `seq` j `seq`
                       case cmp x y of
                         GT -> (j,y)
                         _  -> (i,x)

-- Monadic folds
-- -------------

-- | /O(n)/ Monadic fold
foldM :: (Monad m, Vector v b) => (a -> b -> m a) -> a -> v b -> m a
{-# INLINE foldM #-}
foldM m z = Stream.foldM m z . stream

-- | /O(n)/ Monadic fold over non-empty vectors
fold1M :: (Monad m, Vector v a) => (a -> a -> m a) -> v a -> m a
{-# INLINE fold1M #-}
fold1M m = Stream.fold1M m . stream

-- | /O(n)/ Monadic fold with strict accumulator
foldM' :: (Monad m, Vector v b) => (a -> b -> m a) -> a -> v b -> m a
{-# INLINE foldM' #-}
foldM' m z = Stream.foldM' m z . stream

-- | /O(n)/ Monadic fold over non-empty vectors with strict accumulator
fold1M' :: (Monad m, Vector v a) => (a -> a -> m a) -> v a -> m a
{-# INLINE fold1M' #-}
fold1M' m = Stream.fold1M' m . stream

discard :: Monad m => m a -> m ()
{-# INLINE discard #-}
discard m = m >> return ()

-- | /O(n)/ Monadic fold that discards the result
foldM_ :: (Monad m, Vector v b) => (a -> b -> m a) -> a -> v b -> m ()
{-# INLINE foldM_ #-}
foldM_ m z = discard . Stream.foldM m z . stream

-- | /O(n)/ Monadic fold over non-empty vectors that discards the result
fold1M_ :: (Monad m, Vector v a) => (a -> a -> m a) -> v a -> m ()
{-# INLINE fold1M_ #-}
fold1M_ m = discard . Stream.fold1M m . stream

-- | /O(n)/ Monadic fold with strict accumulator that discards the result
foldM'_ :: (Monad m, Vector v b) => (a -> b -> m a) -> a -> v b -> m ()
{-# INLINE foldM'_ #-}
foldM'_ m z = discard . Stream.foldM' m z . stream

-- | /O(n)/ Monad fold over non-empty vectors with strict accumulator
-- that discards the result
fold1M'_ :: (Monad m, Vector v a) => (a -> a -> m a) -> v a -> m ()
{-# INLINE fold1M'_ #-}
fold1M'_ m = discard . Stream.fold1M' m . stream

-- Monadic sequencing
-- ------------------

-- | Evaluate each action and collect the results
sequence :: (Monad m, Vector v a, Vector v (m a)) => v (m a) -> m (v a)
{-# INLINE sequence #-}
sequence = mapM id

-- | Evaluate each action and discard the results
sequence_ :: (Monad m, Vector v (m a)) => v (m a) -> m ()
{-# INLINE sequence_ #-}
sequence_ = mapM_ id

-- Prefix sums (scans)
-- -------------------

-- | /O(n)/ Prescan
--
-- @
-- prescanl f z = 'init' . 'scanl' f z
-- @
--
-- Example: @prescanl (+) 0 \<1,2,3,4\> = \<0,1,3,6\>@
--
prescanl :: (Vector v a, Vector v b) => (a -> b -> a) -> a -> v b -> v a
{-# INLINE prescanl #-}
prescanl f z = unstream . inplace (MStream.prescanl f z) . stream

-- | /O(n)/ Prescan with strict accumulator
prescanl' :: (Vector v a, Vector v b) => (a -> b -> a) -> a -> v b -> v a
{-# INLINE prescanl' #-}
prescanl' f z = unstream . inplace (MStream.prescanl' f z) . stream

-- | /O(n)/ Scan
--
-- @
-- postscanl f z = 'tail' . 'scanl' f z
-- @
--
-- Example: @postscanl (+) 0 \<1,2,3,4\> = \<1,3,6,10\>@
--
postscanl :: (Vector v a, Vector v b) => (a -> b -> a) -> a -> v b -> v a
{-# INLINE postscanl #-}
postscanl f z = unstream . inplace (MStream.postscanl f z) . stream

-- | /O(n)/ Scan with strict accumulator
postscanl' :: (Vector v a, Vector v b) => (a -> b -> a) -> a -> v b -> v a
{-# INLINE postscanl' #-}
postscanl' f z = unstream . inplace (MStream.postscanl' f z) . stream

-- | /O(n)/ Haskell-style scan
--
-- > scanl f z <x1,...,xn> = <y1,...,y(n+1)>
-- >   where y1 = z
-- >         yi = f y(i-1) x(i-1)
--
-- Example: @scanl (+) 0 \<1,2,3,4\> = \<0,1,3,6,10\>@
-- 
scanl :: (Vector v a, Vector v b) => (a -> b -> a) -> a -> v b -> v a
{-# INLINE scanl #-}
scanl f z = unstream . Stream.scanl f z . stream

-- | /O(n)/ Haskell-style scan with strict accumulator
scanl' :: (Vector v a, Vector v b) => (a -> b -> a) -> a -> v b -> v a
{-# INLINE scanl' #-}
scanl' f z = unstream . Stream.scanl' f z . stream

-- | /O(n)/ Scan over a non-empty vector
--
-- > scanl f <x1,...,xn> = <y1,...,yn>
-- >   where y1 = x1
-- >         yi = f y(i-1) xi
--
scanl1 :: Vector v a => (a -> a -> a) -> v a -> v a
{-# INLINE scanl1 #-}
scanl1 f = unstream . inplace (MStream.scanl1 f) . stream

-- | /O(n)/ Scan over a non-empty vector with a strict accumulator
scanl1' :: Vector v a => (a -> a -> a) -> v a -> v a
{-# INLINE scanl1' #-}
scanl1' f = unstream . inplace (MStream.scanl1' f) . stream

-- | /O(n)/ Right-to-left prescan
--
-- @
-- prescanr f z = 'reverse' . 'prescanl' (flip f) z . 'reverse'
-- @
--
prescanr :: (Vector v a, Vector v b) => (a -> b -> b) -> b -> v a -> v b
{-# INLINE prescanr #-}
prescanr f z = unstreamR . inplace (MStream.prescanl (flip f) z) . streamR

-- | /O(n)/ Right-to-left prescan with strict accumulator
prescanr' :: (Vector v a, Vector v b) => (a -> b -> b) -> b -> v a -> v b
{-# INLINE prescanr' #-}
prescanr' f z = unstreamR . inplace (MStream.prescanl' (flip f) z) . streamR

-- | /O(n)/ Right-to-left scan
postscanr :: (Vector v a, Vector v b) => (a -> b -> b) -> b -> v a -> v b
{-# INLINE postscanr #-}
postscanr f z = unstreamR . inplace (MStream.postscanl (flip f) z) . streamR

-- | /O(n)/ Right-to-left scan with strict accumulator
postscanr' :: (Vector v a, Vector v b) => (a -> b -> b) -> b -> v a -> v b
{-# INLINE postscanr' #-}
postscanr' f z = unstreamR . inplace (MStream.postscanl' (flip f) z) . streamR

-- | /O(n)/ Right-to-left Haskell-style scan
scanr :: (Vector v a, Vector v b) => (a -> b -> b) -> b -> v a -> v b
{-# INLINE scanr #-}
scanr f z = unstreamR . Stream.scanl (flip f) z . streamR

-- | /O(n)/ Right-to-left Haskell-style scan with strict accumulator
scanr' :: (Vector v a, Vector v b) => (a -> b -> b) -> b -> v a -> v b
{-# INLINE scanr' #-}
scanr' f z = unstreamR . Stream.scanl' (flip f) z . streamR

-- | /O(n)/ Right-to-left scan over a non-empty vector
scanr1 :: Vector v a => (a -> a -> a) -> v a -> v a
{-# INLINE scanr1 #-}
scanr1 f = unstreamR . inplace (MStream.scanl1 (flip f)) . streamR

-- | /O(n)/ Right-to-left scan over a non-empty vector with a strict
-- accumulator
scanr1' :: Vector v a => (a -> a -> a) -> v a -> v a
{-# INLINE scanr1' #-}
scanr1' f = unstreamR . inplace (MStream.scanl1' (flip f)) . streamR

-- Conversions - Lists
-- ------------------------

-- | /O(n)/ Convert a vector to a list
toList :: Vector v a => v a -> [a]
{-# INLINE toList #-}
toList = Stream.toList . stream

-- | /O(n)/ Convert a list to a vector
fromList :: Vector v a => [a] -> v a
{-# INLINE fromList #-}
fromList = unstream . Stream.fromList

-- | /O(n)/ Convert the first @n@ elements of a list to a vector
--
-- @
-- fromListN n xs = 'fromList' ('take' n xs)
-- @
fromListN :: Vector v a => Int -> [a] -> v a
{-# INLINE fromListN #-}
fromListN n = unstream . Stream.fromListN n

-- Conversions - Immutable vectors
-- -------------------------------

-- | /O(n)/ Convert different vector types
convert :: (Vector v a, Vector w a) => v a -> w a
{-# INLINE convert #-}
convert = unstream . stream

-- Conversions - Mutable vectors
-- -----------------------------

-- | /O(1)/ Unsafe convert a mutable vector to an immutable one without
-- copying. The mutable vector may not be used after this operation.
unsafeFreeze
  :: (PrimMonad m, Vector v a) => Mutable v (PrimState m) a -> m (v a)
{-# INLINE unsafeFreeze #-}
unsafeFreeze = basicUnsafeFreeze

-- | /O(n)/ Yield an immutable copy of the mutable vector.
freeze :: (PrimMonad m, Vector v a) => Mutable v (PrimState m) a -> m (v a)
{-# INLINE freeze #-}
freeze mv = unsafeFreeze =<< M.clone mv

-- | /O(1)/ Unsafely convert an immutable vector to a mutable one without
-- copying. The immutable vector may not be used after this operation.
unsafeThaw :: (PrimMonad m, Vector v a) => v a -> m (Mutable v (PrimState m) a)
{-# INLINE_STREAM unsafeThaw #-}
unsafeThaw = basicUnsafeThaw

-- | /O(n)/ Yield a mutable copy of the immutable vector.
thaw :: (PrimMonad m, Vector v a) => v a -> m (Mutable v (PrimState m) a)
{-# INLINE_STREAM thaw #-}
thaw v = do
           mv <- M.unsafeNew (length v)
           unsafeCopy mv v
           return mv

{-# RULES

"unsafeThaw/new [Vector]" forall p.
  unsafeThaw (new p) = New.runPrim p

"thaw/new [Vector]" forall p.
  thaw (new p) = New.runPrim p

  #-}

{-
-- | /O(n)/ Yield a mutable vector containing copies of each vector in the
-- list.
thawMany :: (PrimMonad m, Vector v a) => [v a] -> m (Mutable v (PrimState m) a)
{-# INLINE_STREAM thawMany #-}
-- FIXME: add rule for (stream (new (New.create (thawMany vs))))
-- NOTE: We don't try to consume the list lazily as this wouldn't significantly
-- change the space requirements anyway.
thawMany vs = do
                mv <- M.new n
                thaw_loop mv vs
                return mv
  where
    n = List.foldl' (\k v -> k + length v) 0 vs

    thaw_loop mv [] = mv `seq` return ()
    thaw_loop mv (v:vs)
      = do
          let n = length v
          unsafeCopy (M.unsafeTake n mv) v
          thaw_loop (M.unsafeDrop n mv) vs
-}

-- | /O(n)/ Copy an immutable vector into a mutable one. The two vectors must
-- have the same length.
copy
  :: (PrimMonad m, Vector v a) => Mutable v (PrimState m) a -> v a -> m ()
{-# INLINE copy #-}
copy dst src = BOUNDS_CHECK(check) "copy" "length mismatch"
                                          (M.length dst == length src)
             $ unsafeCopy dst src

-- | /O(n)/ Copy an immutable vector into a mutable one. The two vectors must
-- have the same length. This is not checked.
unsafeCopy
  :: (PrimMonad m, Vector v a) => Mutable v (PrimState m) a -> v a -> m ()
{-# INLINE unsafeCopy #-}
unsafeCopy dst src = UNSAFE_CHECK(check) "unsafeCopy" "length mismatch"
                                         (M.length dst == length src)
                   $ (dst `seq` src `seq` basicUnsafeCopy dst src)

-- Conversions to/from Streams
-- ---------------------------

-- | /O(1)/ Convert a vector to a 'Stream'
stream :: Vector v a => v a -> Stream a
{-# INLINE_STREAM stream #-}
stream v = v `seq` n `seq` (Stream.unfoldr get 0 `Stream.sized` Exact n)
  where
    n = length v

    -- NOTE: the False case comes first in Core so making it the recursive one
    -- makes the code easier to read
    {-# INLINE get #-}
    get i | i >= n    = Nothing
          | otherwise = case basicUnsafeIndexM v i of Box x -> Just (x, i+1)

-- | /O(n)/ Construct a vector from a 'Stream'
unstream :: Vector v a => Stream a -> v a
{-# INLINE unstream #-}
unstream s = new (New.unstream s)

{-# RULES

"stream/unstream [Vector]" forall s.
  stream (new (New.unstream s)) = s

"New.unstream/stream [Vector]" forall v.
  New.unstream (stream v) = clone v

"clone/new [Vector]" forall p.
  clone (new p) = p

"inplace [Vector]"
  forall (f :: forall m. Monad m => MStream m a -> MStream m a) m.
  New.unstream (inplace f (stream (new m))) = New.transform f m

"uninplace [Vector]"
  forall (f :: forall m. Monad m => MStream m a -> MStream m a) m.
  stream (new (New.transform f m)) = inplace f (stream (new m))

 #-}

-- | /O(1)/ Convert a vector to a 'Stream', proceeding from right to left
streamR :: Vector v a => v a -> Stream a
{-# INLINE_STREAM streamR #-}
streamR v = v `seq` n `seq` (Stream.unfoldr get n `Stream.sized` Exact n)
  where
    n = length v

    {-# INLINE get #-}
    get 0 = Nothing
    get i = let i' = i-1
            in
            case basicUnsafeIndexM v i' of Box x -> Just (x, i')

-- | /O(n)/ Construct a vector from a 'Stream', proceeding from right to left
unstreamR :: Vector v a => Stream a -> v a
{-# INLINE unstreamR #-}
unstreamR s = new (New.unstreamR s)

{-# RULES

"streamR/unstreamR [Vector]" forall s.
  streamR (new (New.unstreamR s)) = s

"New.unstreamR/streamR/new [Vector]" forall p.
  New.unstreamR (streamR (new p)) = p

"New.unstream/streamR/new [Vector]" forall p.
  New.unstream (streamR (new p)) = New.modify M.reverse p

"New.unstreamR/stream/new [Vector]" forall p.
  New.unstreamR (stream (new p)) = New.modify M.reverse p

"inplace right [Vector]"
  forall (f :: forall m. Monad m => MStream m a -> MStream m a) m.
  New.unstreamR (inplace f (streamR (new m))) = New.transformR f m

"uninplace right [Vector]"
  forall (f :: forall m. Monad m => MStream m a -> MStream m a) m.
  streamR (new (New.transformR f m)) = inplace f (streamR (new m))

 #-}

unstreamM :: (Monad m, Vector v a) => MStream m a -> m (v a)
{-# INLINE_STREAM unstreamM #-}
unstreamM s = do
                xs <- MStream.toList s
                return $ unstream $ Stream.unsafeFromList (MStream.size s) xs

unstreamPrimM :: (PrimMonad m, Vector v a) => MStream m a -> m (v a)
{-# INLINE_STREAM unstreamPrimM #-}
unstreamPrimM s = M.munstream s >>= unsafeFreeze

-- FIXME: the next two functions are only necessary for the specialisations
unstreamPrimM_IO :: Vector v a => MStream IO a -> IO (v a)
{-# INLINE unstreamPrimM_IO #-}
unstreamPrimM_IO = unstreamPrimM

unstreamPrimM_ST :: Vector v a => MStream (ST s) a -> ST s (v a)
{-# INLINE unstreamPrimM_ST #-}
unstreamPrimM_ST = unstreamPrimM

{-# RULES

"unstreamM[IO]" unstreamM = unstreamPrimM_IO
"unstreamM[ST]" unstreamM = unstreamPrimM_ST

 #-}


-- Recycling support
-- -----------------

-- | Construct a vector from a monadic initialiser.
new :: Vector v a => New v a -> v a
{-# INLINE_STREAM new #-}
new m = m `seq` runST (unsafeFreeze =<< New.run m)

-- | Convert a vector to an initialiser which, when run, produces a copy of
-- the vector.
clone :: Vector v a => v a -> New v a
{-# INLINE_STREAM clone #-}
clone v = v `seq` New.create (
  do
    mv <- M.new (length v)
    unsafeCopy mv v
    return mv)

-- Comparisons
-- -----------

-- | /O(n)/ Check if two vectors are equal. All 'Vector' instances are also
-- instances of 'Eq' and it is usually more appropriate to use those. This
-- function is primarily intended for implementing 'Eq' instances for new
-- vector types.
eq :: (Vector v a, Eq a) => v a -> v a -> Bool
{-# INLINE eq #-}
xs `eq` ys = stream xs == stream ys

-- | /O(n)/ Compare two vectors lexicographically. All 'Vector' instances are
-- also instances of 'Ord' and it is usually more appropriate to use those. This
-- function is primarily intended for implementing 'Ord' instances for new
-- vector types.
cmp :: (Vector v a, Ord a) => v a -> v a -> Ordering
{-# INLINE cmp #-}
cmp xs ys = compare (stream xs) (stream ys)

-- Show
-- ----

-- | Generic definition of 'Prelude.showsPrec'
showsPrec :: (Vector v a, Show a) => Int -> v a -> ShowS
{-# INLINE showsPrec #-}
showsPrec p v = showParen (p > 10) $ showString "fromList " . shows (toList v)

-- | Generic definition of 'Text.Read.readPrec'
readPrec :: (Vector v a, Read a) => Read.ReadPrec (v a)
{-# INLINE readPrec #-}
readPrec = Read.parens $ Read.prec 10 $ do
  Read.Ident "fromList" <- Read.lexP
  xs <- Read.readPrec
  return (fromList xs)

-- Data and Typeable
-- -----------------

-- | Generic definion of 'Data.Data.gfoldl' that views a 'Vector' as a
-- list.
gfoldl :: (Vector v a, Data a)
       => (forall d b. Data d => c (d -> b) -> d -> c b)
       -> (forall g. g -> c g)
       -> v a
       -> c (v a)
{-# INLINE gfoldl #-}
gfoldl f z v = z fromList `f` toList v

mkType :: String -> DataType
{-# INLINE mkType #-}
mkType = mkNoRepType

dataCast :: (Vector v a, Data a, Typeable1 v, Typeable1 t)
         => (forall d. Data  d => c (t d)) -> Maybe  (c (v a))
{-# INLINE dataCast #-}
dataCast f = gcast1 f

