{-# LANGUAGE FlexibleInstances, Rank2Types, BangPatterns, CPP #-}

-- |
-- Module      : Data.Vector.Fusion.Stream
-- Copyright   : (c) Roman Leshchinskiy 2008-2010
-- License     : BSD-style
--
-- Maintainer  : Roman Leshchinskiy <rl@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable
-- 
-- Streams for stream fusion
--

module Data.Vector.Fusion.Stream (
  -- * Types
  Step(..), Stream, MStream,

  -- * In-place markers
  inplace,

  -- * Size hints
  size, sized,

  -- * Length information
  length, null,

  -- * Construction
  empty, singleton, cons, snoc, replicate, generate, (++),

  -- * Accessing individual elements
  head, last, (!!), (!?),

  -- * Substreams
  slice, init, tail, take, drop,

  -- * Mapping
  map, concatMap, flatten, unbox,
  
  -- * Zipping
  indexed, indexedR,
  zipWith, zipWith3, zipWith4, zipWith5, zipWith6,
  zip, zip3, zip4, zip5, zip6,

  -- * Filtering
  filter, takeWhile, dropWhile,

  -- * Searching
  elem, notElem, find, findIndex,

  -- * Folding
  foldl, foldl1, foldl', foldl1', foldr, foldr1,

  -- * Specialised folds
  and, or,

  -- * Unfolding
  unfoldr, unfoldrN, iterateN,

  -- * Scans
  prescanl, prescanl',
  postscanl, postscanl',
  scanl, scanl',
  scanl1, scanl1',

  -- * Enumerations
  enumFromStepN, enumFromTo, enumFromThenTo,

  -- * Conversions
  toList, fromList, fromListN, unsafeFromList, liftStream,

  -- * Monadic combinators
  mapM, mapM_, zipWithM, zipWithM_, filterM, foldM, fold1M, foldM', fold1M',

  eq, cmp
) where

import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util
import Data.Vector.Fusion.Stream.Monadic ( Step(..), SPEC(..) )
import qualified Data.Vector.Fusion.Stream.Monadic as M

import Prelude hiding ( length, null,
                        replicate, (++),
                        head, last, (!!),
                        init, tail, take, drop,
                        map, concatMap,
                        zipWith, zipWith3, zip, zip3,
                        filter, takeWhile, dropWhile,
                        elem, notElem,
                        foldl, foldl1, foldr, foldr1,
                        and, or,
                        scanl, scanl1,
                        enumFromTo, enumFromThenTo,
                        mapM, mapM_ )

import GHC.Base ( build )

#include "../../../include/vector.h"

-- | The type of pure streams 
type Stream = M.Stream Id

-- | Alternative name for monadic streams
type MStream = M.Stream

inplace :: (forall m. Monad m => M.Stream m a -> M.Stream m b)
        -> Stream a -> Stream b
{-# INLINE_STREAM inplace #-}
inplace f s = s `seq` f s

{-# RULES

"inplace/inplace [Vector]"
  forall (f :: forall m. Monad m => MStream m a -> MStream m a)
         (g :: forall m. Monad m => MStream m a -> MStream m a)
         s.
  inplace f (inplace g s) = inplace (f . g) s

  #-}

-- | Convert a pure stream to a monadic stream
liftStream :: Monad m => Stream a -> M.Stream m a
{-# INLINE_STREAM liftStream #-}
liftStream (M.Stream step s sz) = M.Stream (return . unId . step) s sz

-- | 'Size' hint of a 'Stream'
size :: Stream a -> Size
{-# INLINE size #-}
size = M.size

-- | Attach a 'Size' hint to a 'Stream'
sized :: Stream a -> Size -> Stream a
{-# INLINE sized #-}
sized = M.sized

-- Length
-- ------

-- | Length of a 'Stream'
length :: Stream a -> Int
{-# INLINE length #-}
length = unId . M.length

-- | Check if a 'Stream' is empty
null :: Stream a -> Bool
{-# INLINE null #-}
null = unId . M.null

-- Construction
-- ------------

-- | Empty 'Stream'
empty :: Stream a
{-# INLINE empty #-}
empty = M.empty

-- | Singleton 'Stream'
singleton :: a -> Stream a
{-# INLINE singleton #-}
singleton = M.singleton

-- | Replicate a value to a given length
replicate :: Int -> a -> Stream a
{-# INLINE replicate #-}
replicate = M.replicate

-- | Generate a stream from its indices
generate :: Int -> (Int -> a) -> Stream a
{-# INLINE generate #-}
generate = M.generate

-- | Prepend an element
cons :: a -> Stream a -> Stream a
{-# INLINE cons #-}
cons = M.cons

-- | Append an element
snoc :: Stream a -> a -> Stream a
{-# INLINE snoc #-}
snoc = M.snoc

infixr 5 ++
-- | Concatenate two 'Stream's
(++) :: Stream a -> Stream a -> Stream a
{-# INLINE (++) #-}
(++) = (M.++)

-- Accessing elements
-- ------------------

-- | First element of the 'Stream' or error if empty
head :: Stream a -> a
{-# INLINE head #-}
head = unId . M.head

-- | Last element of the 'Stream' or error if empty
last :: Stream a -> a
{-# INLINE last #-}
last = unId . M.last

infixl 9 !!
-- | Element at the given position
(!!) :: Stream a -> Int -> a
{-# INLINE (!!) #-}
s !! i = unId (s M.!! i)

infixl 9 !?
-- | Element at the given position or 'Nothing' if out of bounds
(!?) :: Stream a -> Int -> Maybe a
{-# INLINE (!?) #-}
s !? i = unId (s M.!? i)

-- Substreams
-- ----------

-- | Extract a substream of the given length starting at the given position.
slice :: Int   -- ^ starting index
      -> Int   -- ^ length
      -> Stream a
      -> Stream a
{-# INLINE slice #-}
slice = M.slice

-- | All but the last element
init :: Stream a -> Stream a
{-# INLINE init #-}
init = M.init

-- | All but the first element
tail :: Stream a -> Stream a
{-# INLINE tail #-}
tail = M.tail

-- | The first @n@ elements
take :: Int -> Stream a -> Stream a
{-# INLINE take #-}
take = M.take

-- | All but the first @n@ elements
drop :: Int -> Stream a -> Stream a
{-# INLINE drop #-}
drop = M.drop

-- Mapping
-- ---------------

-- | Map a function over a 'Stream'
map :: (a -> b) -> Stream a -> Stream b
{-# INLINE map #-}
map = M.map

unbox :: Stream (Box a) -> Stream a
{-# INLINE unbox #-}
unbox = M.unbox

concatMap :: (a -> Stream b) -> Stream a -> Stream b
{-# INLINE concatMap #-}
concatMap = M.concatMap

-- Zipping
-- -------

-- | Pair each element in a 'Stream' with its index
indexed :: Stream a -> Stream (Int,a)
{-# INLINE indexed #-}
indexed = M.indexed

-- | Pair each element in a 'Stream' with its index, starting from the right
-- and counting down
indexedR :: Int -> Stream a -> Stream (Int,a)
{-# INLINE_STREAM indexedR #-}
indexedR = M.indexedR

-- | Zip two 'Stream's with the given function
zipWith :: (a -> b -> c) -> Stream a -> Stream b -> Stream c
{-# INLINE zipWith #-}
zipWith = M.zipWith

-- | Zip three 'Stream's with the given function
zipWith3 :: (a -> b -> c -> d) -> Stream a -> Stream b -> Stream c -> Stream d
{-# INLINE zipWith3 #-}
zipWith3 = M.zipWith3

zipWith4 :: (a -> b -> c -> d -> e)
                    -> Stream a -> Stream b -> Stream c -> Stream d
                    -> Stream e
{-# INLINE zipWith4 #-}
zipWith4 = M.zipWith4

zipWith5 :: (a -> b -> c -> d -> e -> f)
                    -> Stream a -> Stream b -> Stream c -> Stream d
                    -> Stream e -> Stream f
{-# INLINE zipWith5 #-}
zipWith5 = M.zipWith5

zipWith6 :: (a -> b -> c -> d -> e -> f -> g)
                    -> Stream a -> Stream b -> Stream c -> Stream d
                    -> Stream e -> Stream f -> Stream g
{-# INLINE zipWith6 #-}
zipWith6 = M.zipWith6

zip :: Stream a -> Stream b -> Stream (a,b)
{-# INLINE zip #-}
zip = M.zip

zip3 :: Stream a -> Stream b -> Stream c -> Stream (a,b,c)
{-# INLINE zip3 #-}
zip3 = M.zip3

zip4 :: Stream a -> Stream b -> Stream c -> Stream d
                -> Stream (a,b,c,d)
{-# INLINE zip4 #-}
zip4 = M.zip4

zip5 :: Stream a -> Stream b -> Stream c -> Stream d
                -> Stream e -> Stream (a,b,c,d,e)
{-# INLINE zip5 #-}
zip5 = M.zip5

zip6 :: Stream a -> Stream b -> Stream c -> Stream d
                -> Stream e -> Stream f -> Stream (a,b,c,d,e,f)
{-# INLINE zip6 #-}
zip6 = M.zip6

-- Filtering
-- ---------

-- | Drop elements which do not satisfy the predicate
filter :: (a -> Bool) -> Stream a -> Stream a
{-# INLINE filter #-}
filter = M.filter

-- | Longest prefix of elements that satisfy the predicate
takeWhile :: (a -> Bool) -> Stream a -> Stream a
{-# INLINE takeWhile #-}
takeWhile = M.takeWhile

-- | Drop the longest prefix of elements that satisfy the predicate
dropWhile :: (a -> Bool) -> Stream a -> Stream a
{-# INLINE dropWhile #-}
dropWhile = M.dropWhile

-- Searching
-- ---------

infix 4 `elem`
-- | Check whether the 'Stream' contains an element
elem :: Eq a => a -> Stream a -> Bool
{-# INLINE elem #-}
elem x = unId . M.elem x

infix 4 `notElem`
-- | Inverse of `elem`
notElem :: Eq a => a -> Stream a -> Bool
{-# INLINE notElem #-}
notElem x = unId . M.notElem x

-- | Yield 'Just' the first element matching the predicate or 'Nothing' if no
-- such element exists.
find :: (a -> Bool) -> Stream a -> Maybe a
{-# INLINE find #-}
find f = unId . M.find f

-- | Yield 'Just' the index of the first element matching the predicate or
-- 'Nothing' if no such element exists.
findIndex :: (a -> Bool) -> Stream a -> Maybe Int
{-# INLINE findIndex #-}
findIndex f = unId . M.findIndex f

-- Folding
-- -------

-- | Left fold
foldl :: (a -> b -> a) -> a -> Stream b -> a
{-# INLINE foldl #-}
foldl f z = unId . M.foldl f z

-- | Left fold on non-empty 'Stream's
foldl1 :: (a -> a -> a) -> Stream a -> a
{-# INLINE foldl1 #-}
foldl1 f = unId . M.foldl1 f

-- | Left fold with strict accumulator
foldl' :: (a -> b -> a) -> a -> Stream b -> a
{-# INLINE foldl' #-}
foldl' f z = unId . M.foldl' f z

-- | Left fold on non-empty 'Stream's with strict accumulator
foldl1' :: (a -> a -> a) -> Stream a -> a
{-# INLINE foldl1' #-}
foldl1' f = unId . M.foldl1' f

-- | Right fold
foldr :: (a -> b -> b) -> b -> Stream a -> b
{-# INLINE foldr #-}
foldr f z = unId . M.foldr f z

-- | Right fold on non-empty 'Stream's
foldr1 :: (a -> a -> a) -> Stream a -> a
{-# INLINE foldr1 #-}
foldr1 f = unId . M.foldr1 f

-- Specialised folds
-- -----------------

and :: Stream Bool -> Bool
{-# INLINE and #-}
and = unId . M.and

or :: Stream Bool -> Bool
{-# INLINE or #-}
or = unId . M.or

-- Unfolding
-- ---------

-- | Unfold
unfoldr :: (s -> Maybe (a, s)) -> s -> Stream a
{-# INLINE unfoldr #-}
unfoldr = M.unfoldr

-- | Unfold at most @n@ elements
unfoldrN :: Int -> (s -> Maybe (a, s)) -> s -> Stream a
{-# INLINE unfoldrN #-}
unfoldrN = M.unfoldrN

-- | Apply function n-1 times to value. Zeroth element is original value.
iterateN :: Int -> (a -> a) -> a -> Stream a
{-# INLINE iterateN #-}
iterateN = M.iterateN

-- Scans
-- -----

-- | Prefix scan
prescanl :: (a -> b -> a) -> a -> Stream b -> Stream a
{-# INLINE prescanl #-}
prescanl = M.prescanl

-- | Prefix scan with strict accumulator
prescanl' :: (a -> b -> a) -> a -> Stream b -> Stream a
{-# INLINE prescanl' #-}
prescanl' = M.prescanl'

-- | Suffix scan
postscanl :: (a -> b -> a) -> a -> Stream b -> Stream a
{-# INLINE postscanl #-}
postscanl = M.postscanl

-- | Suffix scan with strict accumulator
postscanl' :: (a -> b -> a) -> a -> Stream b -> Stream a
{-# INLINE postscanl' #-}
postscanl' = M.postscanl'

-- | Haskell-style scan
scanl :: (a -> b -> a) -> a -> Stream b -> Stream a
{-# INLINE scanl #-}
scanl = M.scanl

-- | Haskell-style scan with strict accumulator
scanl' :: (a -> b -> a) -> a -> Stream b -> Stream a
{-# INLINE scanl' #-}
scanl' = M.scanl'

-- | Scan over a non-empty 'Stream'
scanl1 :: (a -> a -> a) -> Stream a -> Stream a
{-# INLINE scanl1 #-}
scanl1 = M.scanl1

-- | Scan over a non-empty 'Stream' with a strict accumulator
scanl1' :: (a -> a -> a) -> Stream a -> Stream a
{-# INLINE scanl1' #-}
scanl1' = M.scanl1'


-- Comparisons
-- -----------

-- FIXME: Move these to Monadic

-- | Check if two 'Stream's are equal
eq :: Eq a => Stream a -> Stream a -> Bool
{-# INLINE_STREAM eq #-}
eq (M.Stream step1 s1 _) (M.Stream step2 s2 _) = eq_loop0 SPEC s1 s2
  where
    eq_loop0 !sPEC s1 s2 = case unId (step1 s1) of
                             Yield x s1' -> eq_loop1 SPEC x s1' s2
                             Skip    s1' -> eq_loop0 SPEC   s1' s2
                             Done        -> null (M.Stream step2 s2 Unknown)

    eq_loop1 !sPEC x s1 s2 = case unId (step2 s2) of
                               Yield y s2' -> x == y && eq_loop0 SPEC   s1 s2'
                               Skip    s2' ->           eq_loop1 SPEC x s1 s2'
                               Done        -> False

-- | Lexicographically compare two 'Stream's
cmp :: Ord a => Stream a -> Stream a -> Ordering
{-# INLINE_STREAM cmp #-}
cmp (M.Stream step1 s1 _) (M.Stream step2 s2 _) = cmp_loop0 SPEC s1 s2
  where
    cmp_loop0 !sPEC s1 s2 = case unId (step1 s1) of
                              Yield x s1' -> cmp_loop1 SPEC x s1' s2
                              Skip    s1' -> cmp_loop0 SPEC   s1' s2
                              Done        -> if null (M.Stream step2 s2 Unknown)
                                               then EQ else LT

    cmp_loop1 !sPEC x s1 s2 = case unId (step2 s2) of
                                Yield y s2' -> case x `compare` y of
                                                 EQ -> cmp_loop0 SPEC s1 s2'
                                                 c  -> c
                                Skip    s2' -> cmp_loop1 SPEC x s1 s2'
                                Done        -> GT

instance Eq a => Eq (M.Stream Id a) where
  {-# INLINE (==) #-}
  (==) = eq

instance Ord a => Ord (M.Stream Id a) where
  {-# INLINE compare #-}
  compare = cmp

-- Monadic combinators
-- -------------------

-- | Apply a monadic action to each element of the stream, producing a monadic
-- stream of results
mapM :: Monad m => (a -> m b) -> Stream a -> M.Stream m b
{-# INLINE mapM #-}
mapM f = M.mapM f . liftStream

-- | Apply a monadic action to each element of the stream
mapM_ :: Monad m => (a -> m b) -> Stream a -> m ()
{-# INLINE mapM_ #-}
mapM_ f = M.mapM_ f . liftStream

zipWithM :: Monad m => (a -> b -> m c) -> Stream a -> Stream b -> M.Stream m c
{-# INLINE zipWithM #-}
zipWithM f as bs = M.zipWithM f (liftStream as) (liftStream bs)

zipWithM_ :: Monad m => (a -> b -> m c) -> Stream a -> Stream b -> m ()
{-# INLINE zipWithM_ #-}
zipWithM_ f as bs = M.zipWithM_ f (liftStream as) (liftStream bs)

-- | Yield a monadic stream of elements that satisfy the monadic predicate
filterM :: Monad m => (a -> m Bool) -> Stream a -> M.Stream m a
{-# INLINE filterM #-}
filterM f = M.filterM f . liftStream

-- | Monadic fold
foldM :: Monad m => (a -> b -> m a) -> a -> Stream b -> m a
{-# INLINE foldM #-}
foldM m z = M.foldM m z . liftStream

-- | Monadic fold over non-empty stream
fold1M :: Monad m => (a -> a -> m a) -> Stream a -> m a
{-# INLINE fold1M #-}
fold1M m = M.fold1M m . liftStream

-- | Monadic fold with strict accumulator
foldM' :: Monad m => (a -> b -> m a) -> a -> Stream b -> m a
{-# INLINE foldM' #-}
foldM' m z = M.foldM' m z . liftStream

-- | Monad fold over non-empty stream with strict accumulator
fold1M' :: Monad m => (a -> a -> m a) -> Stream a -> m a
{-# INLINE fold1M' #-}
fold1M' m = M.fold1M' m . liftStream

-- Enumerations
-- ------------

-- | Yield a 'Stream' of the given length containing the values @x@, @x+y@,
-- @x+y+y@ etc.
enumFromStepN :: Num a => a -> a -> Int -> Stream a
{-# INLINE enumFromStepN #-}
enumFromStepN = M.enumFromStepN

-- | Enumerate values
--
-- /WARNING:/ This operations can be very inefficient. If at all possible, use
-- 'enumFromStepN' instead.
enumFromTo :: Enum a => a -> a -> Stream a
{-# INLINE enumFromTo #-}
enumFromTo = M.enumFromTo

-- | Enumerate values with a given step.
--
-- /WARNING:/ This operations is very inefficient. If at all possible, use
-- 'enumFromStepN' instead.
enumFromThenTo :: Enum a => a -> a -> a -> Stream a
{-# INLINE enumFromThenTo #-}
enumFromThenTo = M.enumFromThenTo

-- Conversions
-- -----------

-- | Convert a 'Stream' to a list
toList :: Stream a -> [a]
{-# INLINE toList #-}
-- toList s = unId (M.toList s)
toList s = build (\c n -> toListFB c n s)

-- This supports foldr/build list fusion that GHC implements
toListFB :: (a -> b -> b) -> b -> Stream a -> b
{-# INLINE [0] toListFB #-}
toListFB c n (M.Stream step s _) = go s
  where
    go s = case unId (step s) of
             Yield x s' -> x `c` go s'
             Skip    s' -> go s'
             Done       -> n

-- | Create a 'Stream' from a list
fromList :: [a] -> Stream a
{-# INLINE fromList #-}
fromList = M.fromList

-- | Create a 'Stream' from the first @n@ elements of a list
--
-- > fromListN n xs = fromList (take n xs)
fromListN :: Int -> [a] -> Stream a
{-# INLINE fromListN #-}
fromListN = M.fromListN

unsafeFromList :: Size -> [a] -> Stream a
{-# INLINE unsafeFromList #-}
unsafeFromList = M.unsafeFromList

-- | Create a 'Stream' of values from a 'Stream' of streamable things
flatten :: (a -> s) -> (s -> Step s b) -> Size -> Stream a -> Stream b
{-# INLINE_STREAM flatten #-}
flatten mk istep sz = M.flatten (return . mk) (return . istep) sz . liftStream

