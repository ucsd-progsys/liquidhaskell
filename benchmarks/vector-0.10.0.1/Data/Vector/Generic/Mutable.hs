{-# LANGUAGE MultiParamTypeClasses, BangPatterns, ScopedTypeVariables, CPP #-}
-- |
-- Module      : Data.Vector.Generic.Mutable
-- Copyright   : (c) Roman Leshchinskiy 2008-2010
-- License     : BSD-style
--
-- Maintainer  : Roman Leshchinskiy <rl@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable
--
-- Generic interface to mutable vectors
--

{-@ LIQUID "--shortnames"     @-}
{-@ LIQUID "--no-termination" @-}

module Data.Vector.Generic.Mutable (
  -- * Class of mutable vector types
  MVector(..),

  -- * Accessors

  -- ** Length information
  length, null,

  -- ** Extracting subvectors
  slice, init, tail, take, drop, splitAt,
  unsafeSlice, unsafeInit, unsafeTail, unsafeTake, unsafeDrop,

  -- ** Overlapping
  overlaps,

  -- * Construction

  -- ** Initialisation
  new, unsafeNew, replicate, replicateM, clone,

  -- ** Growing
  grow, unsafeGrow,

  -- ** Restricting memory usage
  clear,

  -- * Accessing individual elements
  read, write, swap,
  unsafeRead, unsafeWrite, unsafeSwap,

  -- * Modifying vectors

  -- ** Filling and copying
  set, copy, move, unsafeCopy, unsafeMove,

  -- * Internal operations
  mstream, mstreamR,
  unstream, unstreamR,
  munstream, munstreamR,
  transform, transformR,
  fill, fillR,
  unsafeAccum, accum, unsafeUpdate, update, reverse,
  unstablePartition, unstablePartitionStream, partitionStream
) where

import           Language.Haskell.Liquid.Prelude (liquidAssert, liquidAssume)
import qualified Data.Vector.Fusion.Stream      as Stream
import           Data.Vector.Fusion.Stream      ( Stream, MStream )
import qualified Data.Vector.Fusion.Stream.Monadic as MStream
import           Data.Vector.Fusion.Stream.Size
import           Data.Vector.Fusion.Util        ( delay_inline )

import Control.Monad.Primitive ( PrimMonad, PrimState )

import Prelude hiding ( length, null, replicate, reverse, map, read,
                        take, drop, splitAt, init, tail )

#include "../../../include/vector.h"

-- | Class of mutable vectors parametrised with a primitive state token.
--
-- Minimum complete implementation:
--
--   * 'basicLength'
--
--   * 'basicUnsafeSlice'
--
--   * 'basicOverlaps'
--
--   * 'basicUnsafeNew'
--
--   * 'basicUnsafeRead'
--
--   * 'basicUnsafeWrite'
--


{-@ qualif Enlarge(v:Int, x:a): 0  = (mvLen x)                @-}
{-@ qualif Enlarge(v:Int, x:a): v <= (mvLen x)                @-}
{-@ qualif Enlarge(v:Int, x:a): v < (mvLen x)                 @-}
{-@ qualif Enlarge(v:a, x:b): (mvLen x) = (mvLen v)           @-}
{-@ qualif Enlarge(v:a, x:a): (mvLen x) < (mvLen v)           @-}
{-@ qualif GrowBy(v:a, x:a, n:Int): (mvLen v) = (mvLen x) + n @-}
{-@ qualif Size(v:a, n:Int): (mvLen v) = n                    @-}
{-@ qualif Size(v:a, n:Int, m:Int): (mvLen v) = n + m         @-}
{-@ qualif PVec(v:a): 0 <= (mvLen v)                          @-}
{-@ qualif UnsafeAppend1(v:a, i:Int): i < (mvLen v)           @-}


{-@ type PVec v m a        = {x: (v (PrimState m) a) | 0 <= (mvLen x)}    @-}
{-@ type PVecN v m a N     = {x: (PVec v m a) | (mvLen x) = N}            @-}
{-@ type VecAndIx a K      = (a, Int) <{\vec v -> (ValidIx (v-K) vec)}>   @-}
{-@ type PVecV v m a Y     = {x: (PVec v m a) | (mvLen x) = (mvLen Y)}    @-}
{-@ type Pos               = {v:Int | 0 < v }                             @-}
{-@ type NatN N            = {v:Nat | v = N}                              @-}
{-@ predicate ValidIx I V  = (0 <= I && I < (mvLen V))                    @-}
{-@ type OkIx X            = {v:Int | (ValidIx v X)}                      @-}

{-@ predicate SzEq   V X   = (mvLen V) = (mvLen X)                        @-}
{-@ predicate SzPlus V X N = (mvLen V) = (mvLen X) + N                    @-}
{-@ predicate OkSlice V I N = I + N <= (mvLen V)                          @-}
{-@ predicate HasN V N = (OkSlice V 0 N) @-}

{-@ class measure mvLen :: forall a. a -> Int @-}
{-@
class MVector v a where
  basicLength          :: forall s. x:(v s a) -> {v:Nat | v = (mvLen x)}
  basicUnsafeSlice     :: forall s. i:Nat -> n:Nat -> {v: (v s a) | (OkSlice v i n)} -> {v: (v s a) | (mvLen v) = n}
  basicOverlaps        :: forall s. (v s a) -> (v s a) -> Bool
  basicUnsafeNew       :: forall m. PrimMonad m => n:Nat -> (m {x:(v (PrimState m) a) | (mvLen x) = n})
  basicUnsafeReplicate :: forall m. PrimMonad m => n:Nat -> a -> (m (PVecN v m a n))
  basicUnsafeRead      :: forall m. PrimMonad m => x:(v (PrimState m) a) -> (OkIx x) -> (m a)
  basicUnsafeWrite     :: forall m. PrimMonad m => x:(v (PrimState m) a) -> (OkIx x) -> a -> (m ())
  basicClear           :: forall m. PrimMonad m => (v (PrimState m) a) -> (m ())
  basicSet             :: forall m. PrimMonad m => (v (PrimState m) a) -> a -> (m ())
  basicUnsafeCopy      :: forall m. PrimMonad m => dst:(v (PrimState m) a) -> {src:(v (PrimState m) a) | (mvLen src) = (mvLen dst)} -> (m ())
  basicUnsafeMove      :: forall m. PrimMonad m => dst:(v (PrimState m) a) -> {src:(v (PrimState m) a) | (mvLen src) = (mvLen dst)} -> (m ())
  basicUnsafeGrow      :: forall m. PrimMonad m => x:(v (PrimState m) a) -> by:Nat -> (m {v:(v (PrimState m) a) | (SzPlus v x 666)})
@-}


class MVector v a where
  -- | Length of the mutable vector. This method should not be
  -- called directly, use 'length' instead.
  basicLength       :: v s a -> Int

  -- | Yield a part of the mutable vector without copying it. This method
  -- should not be called directly, use 'unsafeSlice' instead.
  basicUnsafeSlice :: Int  -- ^ starting index
                   -> Int  -- ^ length of the slice
                   -> v s a
                   -> v s a

  -- Check whether two vectors overlap. This method should not be
  -- called directly, use 'overlaps' instead.
  basicOverlaps    :: v s a -> v s a -> Bool

  -- | Create a mutable vector of the given length. This method should not be
  -- called directly, use 'unsafeNew' instead.
  basicUnsafeNew   :: PrimMonad m => Int -> m (v (PrimState m) a)

  -- | Create a mutable vector of the given length and fill it with an
  -- initial value. This method should not be called directly, use
  -- 'replicate' instead.
  basicUnsafeReplicate :: PrimMonad m => Int -> a -> m (v (PrimState m) a)

  -- | Yield the element at the given position. This method should not be
  -- called directly, use 'unsafeRead' instead.
  basicUnsafeRead  :: PrimMonad m => v (PrimState m) a -> Int -> m a

  -- | Replace the element at the given position. This method should not be
  -- called directly, use 'unsafeWrite' instead.
  basicUnsafeWrite :: PrimMonad m => v (PrimState m) a -> Int -> a -> m ()

  -- | Reset all elements of the vector to some undefined value, clearing all
  -- references to external objects. This is usually a noop for unboxed
  -- vectors. This method should not be called directly, use 'clear' instead.
  basicClear       :: PrimMonad m => v (PrimState m) a -> m ()

  -- | Set all elements of the vector to the given value. This method should
  -- not be called directly, use 'set' instead.
  basicSet         :: PrimMonad m => v (PrimState m) a -> a -> m ()

  -- | Copy a vector. The two vectors may not overlap. This method should not
  -- be called directly, use 'unsafeCopy' instead.
  basicUnsafeCopy  :: PrimMonad m => v (PrimState m) a   -- ^ target
                                  -> v (PrimState m) a   -- ^ source
                                  -> m ()

  -- | Move the contents of a vector. The two vectors may overlap. This method
  -- should not be called directly, use 'unsafeMove' instead.
  basicUnsafeMove  :: PrimMonad m => v (PrimState m) a   -- ^ target
                                  -> v (PrimState m) a   -- ^ source
                                  -> m ()

  -- | Grow a vector by the given number of elements. This method should not be
  -- called directly, use 'unsafeGrow' instead.
  basicUnsafeGrow  :: PrimMonad m => v (PrimState m) a -> Int
                                                       -> m (v (PrimState m) a)

  {-# INLINE basicUnsafeReplicate #-}
  basicUnsafeReplicate n x
    = do
        v <- basicUnsafeNew n
        basicSet v x
        return v

  {-# INLINE basicClear #-}
  basicClear _ = return ()

  {-# INLINE basicSet #-}
  basicSet !v x
    | n == 0    = return ()
    | otherwise = do
                    basicUnsafeWrite v 0 x
                    do_set 1
    where
      !n = basicLength v

      do_set i | 2*i < n = do basicUnsafeCopy (basicUnsafeSlice i i v)
                                              (basicUnsafeSlice 0 i v)
                              do_set (2*i)
               | otherwise = basicUnsafeCopy (basicUnsafeSlice i (n-i) v)
                                             (basicUnsafeSlice 0 (n-i) v)

  {-# INLINE basicUnsafeCopy #-}
  basicUnsafeCopy !dst !src = do_copy 0
    where
      !n = basicLength src

      do_copy i | i < n = do
                            x <- basicUnsafeRead src i
                            basicUnsafeWrite dst i x
                            do_copy (i+1)
                | otherwise = return ()

  {-# INLINE basicUnsafeMove #-}
  basicUnsafeMove !dst !src
    | basicOverlaps dst src = do
        srcCopy <- clone src
        basicUnsafeCopy dst srcCopy
    | otherwise = basicUnsafeCopy dst src

  {-# INLINE basicUnsafeGrow #-}
  basicUnsafeGrow v by
    = do
        v' <- basicUnsafeNew (n+by)
        basicUnsafeCopy (basicUnsafeSlice 0 n v') v
        return v'
    where
      n = basicLength v

-- ------------------
-- Internal functions
-- ------------------

{-@ unsafeAppend1 :: (PrimMonad m, MVector v a)
        => x:(PVec v m a) -> i:{Nat | i <= (mvLen x)} -> a -> m {v: (PVec v m a) | i < (mvLen v)} @-}

unsafeAppend1 :: (PrimMonad m, MVector v a)
        => v (PrimState m) a -> Int -> a -> m (v (PrimState m) a)
{-# INLINE_INNER unsafeAppend1 #-}
    -- NOTE: The case distinction has to be on the outside because
    -- GHC creates a join point for the unsafeWrite even when everything
    -- is inlined. This is bad because with the join point, v isn't getting
    -- unboxed.
unsafeAppend1 v i x
  | i < length v = do
                     unsafeWrite v i x
                     return v
  | otherwise    = do
                     v' <- enlarge v
                     INTERNAL_CHECK(checkIndex) "unsafeAppend1" i (length v')
                       $ unsafeWrite v' i x
                     return v'


{-@ unsafePrepend1 :: (PrimMonad m, MVector v a)
        => x:(PVec v m a) -> {v:Nat | v <= (mvLen x)} -> a -> m (VecAndIx (PVec v m a) {0}) @-}

unsafePrepend1 :: (PrimMonad m, MVector v a)
        => v (PrimState m) a -> Int -> a -> m (v (PrimState m) a, Int)
{-# INLINE_INNER unsafePrepend1 #-}
unsafePrepend1 v i x
  | i /= 0    = do
                  let i' = i-1
                  unsafeWrite v i' x
                  return (v, i')
  | otherwise = do
                  (v', i) <- enlargeFront v
                  let i' = i-1
                  INTERNAL_CHECK(checkIndex) "unsafePrepend1" i' (length v')
                    $ unsafeWrite v' i' x
                  return (v', i')

mstream :: (PrimMonad m, MVector v a) => v (PrimState m) a -> MStream m a
{-# INLINE mstream #-}
mstream v = v `seq` n `seq` (MStream.unfoldrM get 0 `MStream.sized` Exact n)
  where
    n = length v

    {-# INLINE_INNER get #-}
    get i | i < n     = do x <- unsafeRead v i
                           return $ Just (x, i+1)
          | otherwise = return $ Nothing

{-@ fill :: (PrimMonad m, MVector v a)
              => (PVec v m a) -> MStream m a -> m (PVec v m a) @-}
fill :: (PrimMonad m, MVector v a)
           => v (PrimState m) a -> MStream m a -> m (v (PrimState m) a)
{-# INLINE fill #-}
fill v s = v `seq` do
                     n' <- MStream.foldM put 0 s
                     return $ unsafeSlice 0 n' v
  where
    {-# INLINE_INNER put #-}
    put i' x = do
                 INTERNAL_CHECK(checkIndex) "fill" i (length v)
                   $ unsafeWrite v i x
                 return (i+1)
               where i = liquidAssume (i' < length v) i' -- LIQUID: stream size

{-@ transform :: (PrimMonad m, MVector v a)
      => (MStream m a -> MStream m a) -> (PVec v m a) -> m (PVec v m a) @-}
transform :: (PrimMonad m, MVector v a)
  => (MStream m a -> MStream m a) -> v (PrimState m) a -> m (v (PrimState m) a)
{-# INLINE_STREAM transform #-} -- LIQUID: type application oddity with New.transform (CHECK)
transform f v = fill v (f (mstream v))

mstreamR :: (PrimMonad m, MVector v a) => v (PrimState m) a -> MStream m a
{-# INLINE mstreamR #-}
mstreamR v = v `seq` n `seq` (MStream.unfoldrM get n `MStream.sized` Exact n)
  where
    n = length v

    {-# INLINE_INNER get #-}
    get i | j >= 0    = do x <- unsafeRead v j
                           return $ Just (x,j)
          | otherwise = return Nothing
      where
        j = i-1

{-@ fillR :: (PrimMonad m, MVector v a)
            => (PVec v m a) -> MStream m a -> m (PVec v m a) @-}
fillR :: (PrimMonad m, MVector v a)
           => v (PrimState m) a -> MStream m a -> m (v (PrimState m) a)
{-# INLINE fillR #-}
fillR v s = v `seq` do
                      i <- MStream.foldM put n s
                      return $ unsafeSlice i (n-i) v
  where
    n = length v

    {-# INLINE_INNER put #-}
    put i x = do
                unsafeWrite v j x
                return j
      where
        j = (liquidAssume (i > 0) i) - 1 -- LIQUID: stream

{-@ transformR :: (PrimMonad m, MVector v a)
     => (MStream m a -> MStream m a) -> (PVec v m a) -> m (PVec v m a) @-}
transformR :: (PrimMonad m, MVector v a)
  => (MStream m a -> MStream m a) -> v (PrimState m) a -> m (v (PrimState m) a)
{-# INLINE_STREAM transformR #-}
transformR f v = fillR v (f (mstreamR v))

-- | Create a new mutable vector and fill it with elements from the 'Stream'.
-- The vector will grow exponentially if the maximum size of the 'Stream' is
-- unknown.
unstream :: (PrimMonad m, MVector v a) => Stream a -> m (v (PrimState m) a)
-- NOTE: replace INLINE_STREAM by INLINE? (also in unstreamR)
{-# INLINE_STREAM unstream #-}
unstream s = munstream (Stream.liftStream s)

-- | Create a new mutable vector and fill it with elements from the monadic
-- stream. The vector will grow exponentially if the maximum size of the stream
-- is unknown.
munstream :: (PrimMonad m, MVector v a) => MStream m a -> m (v (PrimState m) a)
{-# INLINE_STREAM munstream #-}
munstream s = case upperBound (MStream.size s) of
               Just n  -> munstreamMax     s n
               Nothing -> munstreamUnknown s

-- FIXME: I can't think of how to prevent GHC from floating out
-- unstreamUnknown. That is bad because SpecConstr then generates two
-- specialisations: one for when it is called from unstream (it doesn't know
-- the shape of the vector) and one for when the vector has grown. To see the
-- problem simply compile this:
--
-- fromList = Data.Vector.Unboxed.unstream . Stream.fromList
--
-- I'm not sure this still applies (19/04/2010)

{-@ munstreamMax
     :: (PrimMonad m, MVector v a) => MStream m a -> Nat -> m (PVec v m a) @-}
munstreamMax
  :: (PrimMonad m, MVector v a) => MStream m a -> Int -> m (v (PrimState m) a)
{-# INLINE munstreamMax #-}
munstreamMax s n
  = do
      v <- INTERNAL_CHECK(checkLength) "munstreamMax" n
           $ unsafeNew n
      let put i' x = do
                        INTERNAL_CHECK(checkIndex) "munstreamMax" i n
                          $ unsafeWrite v i x
                        return (i+1)
                     where i = liquidAssume (i' < n) i -- LIQUID: stream
      n' <- MStream.foldM' put 0 s
      return $ INTERNAL_CHECK(checkSlice) "munstreamMax" 0 n' n
             $ unsafeSlice 0 n' v

{-@ munstreamUnknown
     :: (PrimMonad m, MVector v a) => MStream m a -> m (PVec v m a) @-}

munstreamUnknown
  :: (PrimMonad m, MVector v a) => MStream m a -> m (v (PrimState m) a)
{-# INLINE munstreamUnknown #-}
munstreamUnknown s
  = do
      v <- unsafeNew 0
      (v', n) <- MStream.foldM put (v, 0) s
      return $ INTERNAL_CHECK(checkSlice) "munstreamUnknown" 0 n (length v')
             $ unsafeSlice 0 n v'
  where
    {-# INLINE_INNER put #-}
    put (v,i) x = do
                    v' <- unsafeAppend1 v i x
                    return (v',i+1)

-- | Create a new mutable vector and fill it with elements from the 'Stream'
-- from right to left. The vector will grow exponentially if the maximum size
-- of the 'Stream' is unknown.

{-@ unstreamR :: (PrimMonad m, MVector v a) => Stream a -> m (PVec v m a) @-}
unstreamR :: (PrimMonad m, MVector v a) => Stream a -> m (v (PrimState m) a)
-- NOTE: replace INLINE_STREAM by INLINE? (also in unstream)
{-# INLINE_STREAM unstreamR #-}
unstreamR s = munstreamR (Stream.liftStream s)

-- | Create a new mutable vector and fill it with elements from the monadic
-- stream from right to left. The vector will grow exponentially if the maximum
-- size of the stream is unknown.

{-@ munstreamR :: (PrimMonad m, MVector v a) => MStream m a -> m (PVec v m a) @-}
munstreamR :: (PrimMonad m, MVector v a) => MStream m a -> m (v (PrimState m) a)
{-# INLINE_STREAM munstreamR #-}
munstreamR s = case upperBound (MStream.size s) of
               Just n  -> munstreamRMax     s n
               Nothing -> munstreamRUnknown s

{-@ munstreamRMax
     :: (PrimMonad m, MVector v a) => MStream m a -> Nat -> m (PVec v m a) @-}
munstreamRMax
  :: (PrimMonad m, MVector v a) => MStream m a -> Int -> m (v (PrimState m) a)
{-# INLINE munstreamRMax #-}
munstreamRMax s n
  = do
      v <- INTERNAL_CHECK(checkLength) "munstreamRMax" n
           $ unsafeNew n
      let put i x = do
                      let i' = (liquidAssume (0 < i) i) - 1
                      INTERNAL_CHECK(checkIndex) "munstreamRMax" i' n
                        $ unsafeWrite v i' x
                      return i'
      i <- MStream.foldM' put n s
      return $ INTERNAL_CHECK(checkSlice) "munstreamRMax" i (n-i) n
             $ unsafeSlice i (n-i) v

munstreamRUnknown
  :: (PrimMonad m, MVector v a) => MStream m a -> m (v (PrimState m) a)
{-# INLINE munstreamRUnknown #-}
munstreamRUnknown s
  = do
      v <- unsafeNew 0
      (v', i) <- MStream.foldM put (v, 0) s
      let n = length v'
      return $ INTERNAL_CHECK(checkSlice) "unstreamRUnknown" i (n-i) n
             $ unsafeSlice i (n-i) v'
  where
    {-# INLINE_INNER put #-}
    put (v,i) x = unsafePrepend1 v i x

-- Length
-- ------

-- | Length of the mutable vector.

{-@ length :: MVector v a => x:(v s a) -> {v:Nat | v = (mvLen x)} @-}
length :: MVector v a => v s a -> Int
{-# INLINE length #-}
length = basicLength

-- | Check whether the vector is empty
{-@ null :: MVector v a => x:_ -> {v:Bool | ((Prop v) <=> (mvLen x) = 0)} @-}
null :: MVector v a => v s a -> Bool
{-# INLINE null #-}
null v = length v == 0

-- Extracting subvectors
-- ---------------------

-- | Yield a part of the mutable vector without copying it.

{-@ slice :: (MVector v a) => i:Nat -> n:Nat -> {v:_ | (OkSlice v i n)} -> {v:_ | (mvLen v) = n} @-}

slice :: MVector v a => Int -> Int -> v s a -> v s a
{-# INLINE slice #-}
slice i n v = BOUNDS_CHECK(checkSlice) "slice" i n (length v)
            $ unsafeSlice i n v

take :: MVector v a => Int -> v s a -> v s a
{-# INLINE take #-}
take n v = unsafeSlice 0 (min (max n 0) (length v)) v

drop :: MVector v a => Int -> v s a -> v s a
{-# INLINE drop #-}
drop n v = unsafeSlice (min m n') (max 0 (m - n')) v
  where
    n' = max n 0
    m  = length v

{-# INLINE splitAt #-}
splitAt :: MVector v a => Int -> v s a -> (v s a, v s a)
splitAt n v = ( unsafeSlice 0 m v
              , unsafeSlice m (max 0 (len - n')) v
              )
    where
      m   = min n' len
      n'  = max n 0
      len = length v

{-@ init :: MVector v a => x:{_ | (mvLen x) > 0} -> {v:_ | (mvLen v) = (mvLen x) - 1} @-}
init :: MVector v a => v s a -> v s a
{-# INLINE init #-}
init v = slice 0 (length v - 1) v

{-@ tail :: MVector v a => x:{_ | (mvLen x) > 0} -> {v:_ | (mvLen v) = (mvLen x) - 1} @-}
tail :: MVector v a => v s a -> v s a
{-# INLINE tail #-}
tail v = slice 1 (length v - 1) v

-- | Yield a part of the mutable vector without copying it. No bounds checks
-- are performed.

{-@ unsafeSlice  :: (MVector v a) => i:Nat -> n:Nat -> {v:_ | (OkSlice v i n)} -> {v: _ | (mvLen v) = n} @-}

unsafeSlice :: MVector v a => Int  -- ^ starting index
                           -> Int  -- ^ length of the slice
                           -> v s a
                           -> v s a
{-# INLINE unsafeSlice #-}
unsafeSlice i n v = UNSAFE_CHECK(checkSlice) "unsafeSlice" i n (length v)
                  $ basicUnsafeSlice i n v

{-@ unsafeInit :: MVector v a => x:{(v s a) | (mvLen x) > 0} -> {v: (v s a) | (mvLen v)  = (mvLen x) - 1} @-}
unsafeInit :: MVector v a => v s a -> v s a
{-# INLINE unsafeInit #-}
unsafeInit v = unsafeSlice 0 (length v - 1) v

{-@ unsafeTail :: MVector v a => x:{(v s a) | (mvLen x) > 0} -> {v: (v s a) | (mvLen v)  = (mvLen x) - 1} @-}
unsafeTail :: MVector v a => v s a -> v s a
{-# INLINE unsafeTail #-}
unsafeTail v = unsafeSlice 1 (length v - 1) v

{-@ unsafeTake :: MVector v a => n:Nat -> x:{(v s a) | (HasN x n)} -> {v: (v s a) | (mvLen v) = n} @-}
unsafeTake :: MVector v a => Int -> v s a -> v s a
{-# INLINE unsafeTake #-}
unsafeTake n v = unsafeSlice 0 n v

{-@ unsafeDrop :: MVector v a => n:Nat -> x:{(v s a) | (HasN x n)} -> {v: (v s a) | (mvLen v) = (mvLen x) - n} @-}
unsafeDrop :: MVector v a => Int -> v s a -> v s a
{-# INLINE unsafeDrop #-}
unsafeDrop n v = unsafeSlice n (length v - n) v

-- Overlapping
-- -----------

-- Check whether two vectors overlap.
overlaps :: MVector v a => v s a -> v s a -> Bool
{-# INLINE overlaps #-}
overlaps = basicOverlaps

-- Initialisation
-- --------------

-- | Create a mutable vector of the given length.
{-@ new :: (PrimMonad m, MVector v a) => n:Nat -> m (PVecN v m a n)  @-}
new :: (PrimMonad m, MVector v a) => Int -> m (v (PrimState m) a)
{-# INLINE new #-}
new n = BOUNDS_CHECK(checkLength) "new" n
      $ unsafeNew n

-- | Create a mutable vector of the given length. The length is not checked.
{-@ unsafeNew :: (PrimMonad m, MVector v a) => n:Nat -> m (PVecN v m a n)  @-}
unsafeNew :: (PrimMonad m, MVector v a) => Int -> m (v (PrimState m) a)
{-# INLINE unsafeNew #-}
unsafeNew n = UNSAFE_CHECK(checkLength) "unsafeNew" n
            $ basicUnsafeNew n

-- | Create a mutable vector of the given length (0 if the length is negative)
-- and fill it with an initial value.
{-@ replicate :: (PrimMonad m, MVector v a) => n:Nat -> a -> m (PVecN v m a n) @-}
replicate :: (PrimMonad m, MVector v a) => Int -> a -> m (v (PrimState m) a)
{-# INLINE replicate #-}
replicate n x = basicUnsafeReplicate (delay_inline max 0 n) x

-- | Create a mutable vector of the given length (0 if the length is negative)
-- and fill it with values produced by repeatedly executing the monadic action.
{-@ replicateM :: (PrimMonad m, MVector v a) => n:Nat -> m a -> m (PVecN v m a n) @-}
replicateM :: (PrimMonad m, MVector v a) => Int -> m a -> m (v (PrimState m) a)
{-# INLINE replicateM #-}
replicateM n m = do v <- munstream (MStream.replicateM n m)
                    let v' = liquidAssume (length v == n) v -- LIQUID: stream FAIL
                    return v'


-- | Create a copy of a mutable vector.
{-@ clone :: (PrimMonad m, MVector v a) => x:(PVec v m a) -> m (PVecV v m a x) @-}
clone :: (PrimMonad m, MVector v a) => v (PrimState m) a -> m (v (PrimState m) a)
{-# INLINE clone #-}
clone v = do
            v' <- unsafeNew (length v)
            unsafeCopy v' v
            return v'

-- Growing
-- -------

-- | Grow a vector by the given number of elements. The number must be
-- positive.
{-@ grow :: (PrimMonad m, MVector v a)
                => x:(PVec v m a) -> by:Nat -> m (PVecN v m a {(mvLen x) + by}) @-}
grow :: (PrimMonad m, MVector v a)
                => v (PrimState m) a -> Int -> m (v (PrimState m) a)
{-# INLINE grow #-}
grow v by = BOUNDS_CHECK(checkLength) "grow" by
          $ unsafeGrow v by

growFront :: (PrimMonad m, MVector v a)
                => v (PrimState m) a -> Int -> m (v (PrimState m) a)
{-# INLINE growFront #-}
growFront v by = BOUNDS_CHECK(checkLength) "growFront" by
               $ unsafeGrowFront v by

{-@ enlarge_delta :: (MVector v a) => x:(v s a) -> {v:Pos | (mvLen x) <= v} @-}
enlarge_delta v = max (length v) 1

-- | Grow a vector logarithmically
{-@ enlarge :: (PrimMonad m, MVector v a) => x:(PVec v m a) -> (m {v:(PVec v m a) | (mvLen x) < (mvLen v)}) @-}
enlarge :: (PrimMonad m, MVector v a)
                => v (PrimState m) a -> m (v (PrimState m) a)
{-# INLINE enlarge #-}
enlarge v = unsafeGrow v (enlarge_delta v)

{-@ enlargeFront :: (PrimMonad m, MVector v a) => x:(PVec v m a) -> (m (VecAndIx {v:(PVec v m a) | (mvLen x) < (mvLen v)} {1})) @-}
enlargeFront :: (PrimMonad m, MVector v a)
                => v (PrimState m) a -> m (v (PrimState m) a, Int)
{-# INLINE enlargeFront #-}
enlargeFront v = do
                   v' <- unsafeGrowFront v by
                   return (v', by)
  where
    by = enlarge_delta v

-- | Grow a vector by the given number of elements. The number must be
-- positive but this is not checked.

{-@ unsafeGrow :: (PrimMonad m, MVector v a) => x: (PVec v m a) -> n:Nat -> (m (PVecN v m a {(mvLen x) + n})) @-}
unsafeGrow :: (PrimMonad m, MVector v a)
                        => v (PrimState m) a -> Int -> m (v (PrimState m) a)
{-# INLINE unsafeGrow #-}
unsafeGrow v n = UNSAFE_CHECK(checkLength) "unsafeGrow" n
               $ basicUnsafeGrow v n


{-@ unsafeGrowFront :: (PrimMonad m, MVector v a)
                        => x:(v (PrimState m) a) -> n:Nat -> (m (PVecN v m a {(mvLen x) + n})) @-}
unsafeGrowFront :: (PrimMonad m, MVector v a)
                        => v (PrimState m) a -> Int -> m (v (PrimState m) a)
{-# INLINE unsafeGrowFront #-}
unsafeGrowFront v by = UNSAFE_CHECK(checkLength) "unsafeGrowFront" by
                     $ do
                         let n = length v
                         v' <- basicUnsafeNew (by+n)
                         basicUnsafeCopy (basicUnsafeSlice by n v') v
                         return v'

-- Restricting memory usage
-- ------------------------

-- | Reset all elements of the vector to some undefined value, clearing all
-- references to external objects. This is usually a noop for unboxed vectors.
clear :: (PrimMonad m, MVector v a) => v (PrimState m) a -> m ()
{-# INLINE clear #-}
clear = basicClear

-- Accessing individual elements
-- -----------------------------

-- | Yield the element at the given position.
{-@ read :: (PrimMonad m, MVector v a) => x:(PVec v m a) -> (OkIx x) -> m a @-}
read :: (PrimMonad m, MVector v a) => v (PrimState m) a -> Int -> m a
{-# INLINE read #-}
read v i = BOUNDS_CHECK(checkIndex) "read" i (length v)
         $ unsafeRead v i

-- | Replace the element at the given position.
{-@ write :: (PrimMonad m, MVector v a) => x:(PVec v m a) -> (OkIx x)-> a -> m () @-}
write :: (PrimMonad m, MVector v a) => v (PrimState m) a -> Int -> a -> m ()
{-# INLINE write #-}
write v i x = BOUNDS_CHECK(checkIndex) "write" i (length v)
            $ unsafeWrite v i x

-- | Swap the elements at the given positions.
{-@ swap :: (PrimMonad m, MVector v a) => x:(PVec v m a) -> (OkIx x) -> (OkIx x) -> m () @-}
swap :: (PrimMonad m, MVector v a) => v (PrimState m) a -> Int -> Int -> m ()
{-# INLINE swap #-}
swap v i j = BOUNDS_CHECK(checkIndex) "swap" i (length v)
           $ BOUNDS_CHECK(checkIndex) "swap" j (length v)
           $ unsafeSwap v i j

-- | Replace the element at the give position and return the old element.
{-@ exchange :: (PrimMonad m, MVector v a) => x:(PVec v m a) -> (OkIx x) -> a -> m a @-}
exchange :: (PrimMonad m, MVector v a) => v (PrimState m) a -> Int -> a -> m a
{-# INLINE exchange #-}
exchange v i x = BOUNDS_CHECK(checkIndex) "exchange" i (length v)
               $ unsafeExchange v i x

-- | Yield the element at the given position. No bounds checks are performed.
{-@ unsafeRead :: (PrimMonad m, MVector v a) => x:(PVec v m a) -> (OkIx x) -> m a @-}
unsafeRead :: (PrimMonad m, MVector v a) => v (PrimState m) a -> Int -> m a
{-# INLINE unsafeRead #-}
unsafeRead v i = UNSAFE_CHECK(checkIndex) "unsafeRead" i (length v)
               $ basicUnsafeRead v i

-- | Replace the element at the given position. No bounds checks are performed.
{-@ unsafeWrite :: (PrimMonad m, MVector v a)
                                => x:(v (PrimState m) a) -> (OkIx x) -> a -> (m ()) @-}
unsafeWrite :: (PrimMonad m, MVector v a)
                                => v (PrimState m) a -> Int -> a -> m ()
{-# INLINE unsafeWrite #-}
unsafeWrite v i x = UNSAFE_CHECK(checkIndex) "unsafeWrite" i (length v)
                  $ basicUnsafeWrite v i x

-- | Swap the elements at the given positions. No bounds checks are performed.
{-@ unsafeSwap :: (PrimMonad m, MVector v a)
                => x:(PVec v m a) -> (OkIx x) -> (OkIx x) -> m () @-}
unsafeSwap :: (PrimMonad m, MVector v a)
                => v (PrimState m) a -> Int -> Int -> m ()
{-# INLINE unsafeSwap #-}
unsafeSwap v i j = UNSAFE_CHECK(checkIndex) "unsafeSwap" i (length v)
                 $ UNSAFE_CHECK(checkIndex) "unsafeSwap" j (length v)
                 $ do
                     x <- unsafeRead v i
                     y <- unsafeRead v j
                     unsafeWrite v i y
                     unsafeWrite v j x

-- | Replace the element at the give position and return the old element. No
-- bounds checks are performed.
{-@ unsafeExchange :: (PrimMonad m, MVector v a)
                                => x:(PVec v m a) -> (OkIx x) -> a -> m a @-}
unsafeExchange :: (PrimMonad m, MVector v a)
                                => v (PrimState m) a -> Int -> a -> m a
{-# INLINE unsafeExchange #-}
unsafeExchange v i x = UNSAFE_CHECK(checkIndex) "unsafeExchange" i (length v)
                     $ do
                         y <- unsafeRead v i
                         unsafeWrite v i x
                         return y

-- Filling and copying
-- -------------------

-- | Set all elements of the vector to the given value.
set :: (PrimMonad m, MVector v a) => v (PrimState m) a -> a -> m ()
{-# INLINE set #-}
set = basicSet

-- | Copy a vector. The two vectors must have the same length and may not
-- overlap.

{-@ copy :: (PrimMonad m, MVector v a)
                => dst:(PVec v m a) -> src:(PVecV v m a dst) -> m () @-}
copy :: (PrimMonad m, MVector v a)
                => v (PrimState m) a -> v (PrimState m) a -> m ()
{-# INLINE copy #-}
copy dst src = BOUNDS_CHECK(checkLIQUID) "copy" "overlapping vectors"
                                          (not (dst `overlaps` src))
             $ BOUNDS_CHECK(check) "copy" "length mismatch"
                                          (length dst == length src)
             $ unsafeCopy dst src

-- | Move the contents of a vector. The two vectors must have the same
-- length.
--
-- If the vectors do not overlap, then this is equivalent to 'copy'.
-- Otherwise, the copying is performed as if the source vector were
-- copied to a temporary vector and then the temporary vector was copied
-- to the target vector.

{-@ move :: (PrimMonad m, MVector v a)
                => dst:(PVec v m a) -> src:(PVecV v m a dst) -> m () @-}

move :: (PrimMonad m, MVector v a)
                => v (PrimState m) a -> v (PrimState m) a -> m ()
{-# INLINE move #-}
move dst src = BOUNDS_CHECK(check) "move" "length mismatch"
                                          (length dst == length src)
             $ unsafeMove dst src

-- | Copy a vector. The two vectors must have the same length and may not
-- overlap. This is not checked.

{-@ unsafeCopy :: (PrimMonad m, MVector v a)
               => dst:(PVec v m a) -> src:(PVecV v m a dst) -> m () @-}
unsafeCopy :: (PrimMonad m, MVector v a) => v (PrimState m) a   -- ^ target
                                         -> v (PrimState m) a   -- ^ source
                                         -> m ()
{-# INLINE unsafeCopy #-}
unsafeCopy dst src = UNSAFE_CHECK(check) "unsafeCopy" "length mismatch"
                                         (length dst == length src)
                   $ UNSAFE_CHECK(checkLIQUID) "unsafeCopy" "overlapping vectors"
                                         (not (dst `overlaps` src))
                   $ (dst `seq` src `seq` basicUnsafeCopy dst src)

-- | Move the contents of a vector. The two vectors must have the same
-- length, but this is not checked.
--
-- If the vectors do not overlap, then this is equivalent to 'unsafeCopy'.
-- Otherwise, the copying is performed as if the source vector were
-- copied to a temporary vector and then the temporary vector was copied
-- to the target vector.

{-@ unsafeMove :: (PrimMonad m, MVector v a) => dst:(PVec v m a)
                                             -> src:(PVecV v m a dst)
                                             -> m ()
  @-}

unsafeMove :: (PrimMonad m, MVector v a) => v (PrimState m) a   -- ^ target
                                         -> v (PrimState m) a   -- ^ source
                                         -> m ()
{-# INLINE unsafeMove #-}
unsafeMove dst src = UNSAFE_CHECK(check) "unsafeMove" "length mismatch"
                                         (length dst == length src)
                   $ (dst `seq` src `seq` basicUnsafeMove dst src)

-- Permutations
-- ------------
{-@ accum :: (PrimMonad m, MVector v a)
        => (a -> b -> a) -> x:_ -> Stream ((OkIx x), b) -> m () @-}
accum :: (PrimMonad m, MVector v a)
        => (a -> b -> a) -> v (PrimState m) a -> Stream (Int, b) -> m ()
{-# INLINE accum #-}
accum f !v s = Stream.mapM_ upd s
  where
    {-# INLINE_INNER upd #-}
    upd (i,b) = do
                  a <- BOUNDS_CHECK(checkIndex) "accum" i n
                     $ unsafeRead v i
                  unsafeWrite v i (f a b)

    !n = length v

{-@ update :: (PrimMonad m, MVector v a)
                        => x:_ -> Stream ((OkIx x), a) -> m () @-}
update :: (PrimMonad m, MVector v a)
                        => v (PrimState m) a -> Stream (Int, a) -> m ()
{-# INLINE update #-}
update !v s = Stream.mapM_ upd s
  where
    {-# INLINE_INNER upd #-}
    upd (i,b) = BOUNDS_CHECK(checkIndex) "update" i n
              $ unsafeWrite v i b

    !n = length v

{-@ unsafeAccum :: (PrimMonad m, MVector v a)
            => (a -> b -> a) -> x:_ -> Stream ((OkIx x), b) -> m () @-}
unsafeAccum :: (PrimMonad m, MVector v a)
            => (a -> b -> a) -> v (PrimState m) a -> Stream (Int, b) -> m ()
{-# INLINE unsafeAccum #-}
unsafeAccum f !v s = Stream.mapM_ upd s
  where
    {-# INLINE_INNER upd #-}
    upd (i,b) = do
                  a <- UNSAFE_CHECK(checkIndex) "accum" i n
                     $ unsafeRead v i
                  unsafeWrite v i (f a b)

    !n = length v

{-@ unsafeUpdate :: (PrimMonad m, MVector v a)
                        => x:_  -> Stream ((OkIx x), a) -> m () @-}
unsafeUpdate :: (PrimMonad m, MVector v a)
                        => v (PrimState m) a -> Stream (Int, a) -> m ()
{-# INLINE unsafeUpdate #-}
unsafeUpdate !v s = Stream.mapM_ upd s
  where
    {-# INLINE_INNER upd #-}
    upd (i,b) = UNSAFE_CHECK(checkIndex) "accum" i n
                  $ unsafeWrite v i b

    !n = length v

reverse :: (PrimMonad m, MVector v a) => v (PrimState m) a -> m ()
{-# INLINE reverse #-}
reverse !v = reverse_loop 0 (length v - 1)
  where
    reverse_loop i j | i < j = do
                                 unsafeSwap v i j
                                 reverse_loop (i + 1) (j - 1)
    reverse_loop _ _ = return ()

unstablePartition :: forall m v a. (PrimMonad m, MVector v a)
                  => (a -> Bool) -> v (PrimState m) a -> m Int
{-# INLINE unstablePartition #-}
unstablePartition f !v = from_left 0 (length v)
  where
    -- NOTE: GHC 6.10.4 panics without the signatures on from_left and
    -- from_right
    from_left :: Int -> Int -> m Int
    from_left i j
      | i == j    = return i
      | otherwise = do
                      x <- unsafeRead v i
                      if f x
                        then from_left (i+1) j
                        else from_right i (j-1)

    from_right :: Int -> Int -> m Int
    from_right i j
      | i == j    = return i
      | otherwise = do
                      x <- unsafeRead v j
                      if f x
                        then do
                               y <- unsafeRead v i
                               unsafeWrite v i x
                               unsafeWrite v j y
                               from_left (i+1) j
                        else from_right i (j-1)

{-@ unstablePartitionMax :: (PrimMonad m, MVector v a)
        => (a -> Bool) -> Stream a -> n:Nat
        -> m ((PVec v m a), (PVec v m a)) @-} -- some glitch prevents this: <{\x1 x2 -> (mvLen x1) + (mvLen x2) <= n}>) @-}

unstablePartitionStream :: (PrimMonad m, MVector v a)
        => (a -> Bool) -> Stream a -> m (v (PrimState m) a, v (PrimState m) a)
{-# INLINE unstablePartitionStream #-}
unstablePartitionStream f s
  = case upperBound (Stream.size s) of
      Just n  -> unstablePartitionMax f s n
      Nothing -> partitionUnknown f s

unstablePartitionMax :: (PrimMonad m, MVector v a)
        => (a -> Bool) -> Stream a -> Int
        -> m (v (PrimState m) a, v (PrimState m) a)
{-# INLINE unstablePartitionMax #-}
unstablePartitionMax f s n
  = do
      v <- INTERNAL_CHECK(checkLength) "unstablePartitionMax" n
           $ unsafeNew n
      let {-# INLINE_INNER put #-}
          put (i', j') x
            | f x       = do
                            unsafeWrite v i x
                            return (i+1, j)
            | otherwise = do
                            unsafeWrite v (j-1) x
                            return (i, j-1)
            where
              i = liquidAssume (i' < j') i' -- LIQUID: stream
              j = liquidAssume (i' < j') j' -- LIQUID: stream

      (i,j) <- Stream.foldM' put (0, n) s
      return (unsafeSlice 0 i v, unsafeSlice j (n-j) v)

partitionStream :: (PrimMonad m, MVector v a)
        => (a -> Bool) -> Stream a -> m (v (PrimState m) a, v (PrimState m) a)
{-# INLINE partitionStream #-}
partitionStream f s
  = case upperBound (Stream.size s) of
      Just n  -> partitionMax f s n
      Nothing -> partitionUnknown f s


{-@ partitionMax :: (PrimMonad m, MVector v a)
        => (a -> Bool) -> Stream a -> n:Nat -> m ((PVec v m a), (PVec v m a)) @-}
partitionMax :: (PrimMonad m, MVector v a)
  => (a -> Bool) -> Stream a -> Int -> m (v (PrimState m) a, v (PrimState m) a)
{-# INLINE partitionMax #-}
partitionMax f s n
  = do
      v <- INTERNAL_CHECK(checkLength) "unstablePartitionMax" n
         $ unsafeNew n

      let {-# INLINE_INNER put #-}
          put (i'', j'') x
            | f x       = do
                            unsafeWrite v i x
                            return (i+1,j)

            | otherwise = let j' = j-1 in
                          do
                            unsafeWrite v j' x
                            return (i,j')
            where
              i = liquidAssume (i'' < j'') i''
              j = liquidAssume (i'' < j'') j''

      (i,j) <- Stream.foldM' put (0,n) s
      INTERNAL_CHECK(check) "partitionMax" "invalid indices" (i <= j)
        $ return ()
      let l = unsafeSlice 0 i v
          r = unsafeSlice j (n-j) v
      reverse r
      return (l,r)

partitionUnknown :: (PrimMonad m, MVector v a)
        => (a -> Bool) -> Stream a -> m (v (PrimState m) a, v (PrimState m) a)
{-# INLINE partitionUnknown #-}
partitionUnknown f s
  = do
      v1 <- unsafeNew 0
      v2 <- unsafeNew 0
      (v1', n1, v2', n2) <- Stream.foldM' put (v1, 0, v2, 0) s
      INTERNAL_CHECK(checkSlice) "partitionUnknown" 0 n1 (length v1')
        $ INTERNAL_CHECK(checkSlice) "partitionUnknown" 0 n2 (length v2')
        $ return (unsafeSlice 0 n1 v1', unsafeSlice 0 n2 v2')
  where
    -- NOTE: The case distinction has to be on the outside because
    -- GHC creates a join point for the unsafeWrite even when everything
    -- is inlined. This is bad because with the join point, v isn't getting
    -- unboxed.
    {-# INLINE_INNER put #-}
    put (v1, i1, v2, i2) x
      | f x       = do
                      v1' <- unsafeAppend1 v1 i1 x
                      return (v1', i1+1, v2, i2)
      | otherwise = do
                      v2' <- unsafeAppend1 v2 i2 x
                      return (v1, i1, v2', i2+1)
