{-# LANGUAGE ExistentialQuantification, Rank2Types, BangPatterns #-}

-- |
-- Module      : Data.Vector.Fusion.Stream.Monadic
-- Copyright   : (c) Roman Leshchinskiy 2008-2010
-- License     : BSD-style
--
-- Maintainer  : Roman Leshchinskiy <rl@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable
--
-- Monadic stream combinators.
--

module Data.Vector.Fusion.Stream.Monadic (
  Stream(..), Step(..), SPEC(..),

  -- * Size hints
  size, sized,

  -- * Length
  length, null,

  -- * Construction
  empty, singleton, cons, snoc, replicate, replicateM, generate, generateM, (++),

  -- * Accessing elements
  head, last, (!!), (!?),

  -- * Substreams
  slice, init, tail, take, drop,

  -- * Mapping
  map, mapM, mapM_, trans, unbox, concatMap, flatten,
  
  -- * Zipping
  indexed, indexedR, zipWithM_,
  zipWithM, zipWith3M, zipWith4M, zipWith5M, zipWith6M,
  zipWith, zipWith3, zipWith4, zipWith5, zipWith6,
  zip, zip3, zip4, zip5, zip6,

  -- * Filtering
  filter, filterM, takeWhile, takeWhileM, dropWhile, dropWhileM,

  -- * Searching
  elem, notElem, find, findM, findIndex, findIndexM,

  -- * Folding
  foldl, foldlM, foldl1, foldl1M, foldM, fold1M,
  foldl', foldlM', foldl1', foldl1M', foldM', fold1M',
  foldr, foldrM, foldr1, foldr1M,

  -- * Specialised folds
  and, or, concatMapM,

  -- * Unfolding
  unfoldr, unfoldrM,
  unfoldrN, unfoldrNM,
  iterateN, iterateNM,

  -- * Scans
  prescanl, prescanlM, prescanl', prescanlM',
  postscanl, postscanlM, postscanl', postscanlM',
  scanl, scanlM, scanl', scanlM',
  scanl1, scanl1M, scanl1', scanl1M',

  -- * Enumerations
  enumFromStepN, enumFromTo, enumFromThenTo,

  -- * Conversions
  toList, fromList, fromListN, unsafeFromList
) where

import Data.Vector.Fusion.Stream.Size
import Data.Vector.Fusion.Util ( Box(..), delay_inline )

import Data.Char      ( ord )
import GHC.Base       ( unsafeChr )
import Control.Monad  ( liftM )
import Prelude hiding ( length, null,
                        replicate, (++),
                        head, last, (!!),
                        init, tail, take, drop,
                        map, mapM, mapM_, concatMap,
                        zipWith, zipWith3, zip, zip3,
                        filter, takeWhile, dropWhile,
                        elem, notElem,
                        foldl, foldl1, foldr, foldr1,
                        and, or,
                        scanl, scanl1,
                        enumFromTo, enumFromThenTo )

import Data.Int  ( Int8, Int16, Int32, Int64 )
import Data.Word ( Word8, Word16, Word32, Word, Word64 )

#if __GLASGOW_HASKELL__ >= 700
import GHC.Exts ( SpecConstrAnnotation(..) )
#endif

#include "vector.h"

data SPEC = SPEC | SPEC2
#if __GLASGOW_HASKELL__ >= 700
{-# ANN type SPEC ForceSpecConstr #-}
#endif

emptyStream :: String
{-# NOINLINE emptyStream #-}
emptyStream = "empty stream"

#define EMPTY_STREAM (\s -> ERROR s emptyStream)

-- | Result of taking a single step in a stream
data Step s a = Yield a s  -- ^ a new element and a new seed
              | Skip    s  -- ^ just a new seed
              | Done       -- ^ end of stream

-- | Monadic streams
data Stream m a = forall s. Stream (s -> m (Step s a)) s Size

-- | 'Size' hint of a 'Stream'
size :: Stream m a -> Size
{-# INLINE size #-}
size (Stream _ _ sz) = sz

-- | Attach a 'Size' hint to a 'Stream'
sized :: Stream m a -> Size -> Stream m a
{-# INLINE_STREAM sized #-}
sized (Stream step s _) sz = Stream step s sz

-- Length
-- ------

-- | Length of a 'Stream'
length :: Monad m => Stream m a -> m Int
{-# INLINE_STREAM length #-}
length s = foldl' (\n _ -> n+1) 0 s

-- | Check if a 'Stream' is empty
null :: Monad m => Stream m a -> m Bool
{-# INLINE_STREAM null #-}
null s = foldr (\_ _ -> False) True s


-- Construction
-- ------------

-- | Empty 'Stream'
empty :: Monad m => Stream m a
{-# INLINE_STREAM empty #-}
empty = Stream (const (return Done)) () (Exact 0)

-- | Singleton 'Stream'
singleton :: Monad m => a -> Stream m a
{-# INLINE_STREAM singleton #-}
singleton x = Stream (return . step) True (Exact 1)
  where
    {-# INLINE_INNER step #-}
    step True  = Yield x False
    step False = Done

-- | Replicate a value to a given length
replicate :: Monad m => Int -> a -> Stream m a
{-# INLINE replicate #-}
replicate n x = replicateM n (return x)

-- | Yield a 'Stream' of values obtained by performing the monadic action the
-- given number of times
replicateM :: Monad m => Int -> m a -> Stream m a
{-# INLINE_STREAM replicateM #-}
-- NOTE: We delay inlining max here because GHC will create a join point for
-- the call to newArray# otherwise which is not really nice.
replicateM n p = Stream step n (Exact (delay_inline max n 0))
  where
    {-# INLINE_INNER step #-}
    step i | i <= 0    = return Done
           | otherwise = do { x <- p; return $ Yield x (i-1) }

generate :: Monad m => Int -> (Int -> a) -> Stream m a
{-# INLINE generate #-}
generate n f = generateM n (return . f)

-- | Generate a stream from its indices
generateM :: Monad m => Int -> (Int -> m a) -> Stream m a
{-# INLINE_STREAM generateM #-}
generateM n f = n `seq` Stream step 0 (Exact (delay_inline max n 0))
  where
    {-# INLINE_INNER step #-}
    step i | i < n     = do
                           x <- f i
                           return $ Yield x (i+1)
           | otherwise = return Done

-- | Prepend an element
cons :: Monad m => a -> Stream m a -> Stream m a
{-# INLINE cons #-}
cons x s = singleton x ++ s

-- | Append an element
snoc :: Monad m => Stream m a -> a -> Stream m a
{-# INLINE snoc #-}
snoc s x = s ++ singleton x

infixr 5 ++
-- | Concatenate two 'Stream's
(++) :: Monad m => Stream m a -> Stream m a -> Stream m a
{-# INLINE_STREAM (++) #-}
Stream stepa sa na ++ Stream stepb sb nb = Stream step (Left sa) (na + nb)
  where
    {-# INLINE_INNER step #-}
    step (Left  sa) = do
                        r <- stepa sa
                        case r of
                          Yield x sa' -> return $ Yield x (Left  sa')
                          Skip    sa' -> return $ Skip    (Left  sa')
                          Done        -> return $ Skip    (Right sb)
    step (Right sb) = do
                        r <- stepb sb
                        case r of
                          Yield x sb' -> return $ Yield x (Right sb')
                          Skip    sb' -> return $ Skip    (Right sb')
                          Done        -> return $ Done

-- Accessing elements
-- ------------------

-- | First element of the 'Stream' or error if empty
head :: Monad m => Stream m a -> m a
{-# INLINE_STREAM head #-}
head (Stream step s _) = head_loop SPEC s
  where
    head_loop !sPEC s
      = do
          r <- step s
          case r of
            Yield x _  -> return x
            Skip    s' -> head_loop SPEC s'
            Done       -> EMPTY_STREAM "head"



-- | Last element of the 'Stream' or error if empty
last :: Monad m => Stream m a -> m a
{-# INLINE_STREAM last #-}
last (Stream step s _) = last_loop0 SPEC s
  where
    last_loop0 !sPEC s
      = do
          r <- step s
          case r of
            Yield x s' -> last_loop1 SPEC x s'
            Skip    s' -> last_loop0 SPEC   s'
            Done       -> EMPTY_STREAM "last"

    last_loop1 !sPEC x s
      = do
          r <- step s
          case r of
            Yield y s' -> last_loop1 SPEC y s'
            Skip    s' -> last_loop1 SPEC x s'
            Done       -> return x

infixl 9 !!
-- | Element at the given position
(!!) :: Monad m => Stream m a -> Int -> m a
{-# INLINE (!!) #-}
Stream step s _ !! i | i < 0     = ERROR "!!" "negative index"
                     | otherwise = index_loop SPEC s i
  where
    index_loop !sPEC s i
      = i `seq`
        do
          r <- step s
          case r of
            Yield x s' | i == 0    -> return x
                       | otherwise -> index_loop SPEC s' (i-1)
            Skip    s'             -> index_loop SPEC s' i
            Done                   -> EMPTY_STREAM "!!"

infixl 9 !?
-- | Element at the given position or 'Nothing' if out of bounds
(!?) :: Monad m => Stream m a -> Int -> m (Maybe a)
{-# INLINE (!?) #-}
Stream step s _ !? i = index_loop SPEC s i
  where
    index_loop !sPEC s i
      = i `seq`
        do
          r <- step s
          case r of
            Yield x s' | i == 0    -> return (Just x)
                       | otherwise -> index_loop SPEC s' (i-1)
            Skip    s'             -> index_loop SPEC s' i
            Done                   -> return Nothing

-- Substreams
-- ----------

-- | Extract a substream of the given length starting at the given position.
slice :: Monad m => Int   -- ^ starting index
                 -> Int   -- ^ length
                 -> Stream m a
                 -> Stream m a
{-# INLINE slice #-}
slice i n s = take n (drop i s)

-- | All but the last element
init :: Monad m => Stream m a -> Stream m a
{-# INLINE_STREAM init #-}
init (Stream step s sz) = Stream step' (Nothing, s) (sz - 1)
  where
    {-# INLINE_INNER step' #-}
    step' (Nothing, s) = liftM (\r ->
                           case r of
                             Yield x s' -> Skip (Just x,  s')
                             Skip    s' -> Skip (Nothing, s')
                             Done       -> EMPTY_STREAM "init"
                         ) (step s)

    step' (Just x,  s) = liftM (\r -> 
                           case r of
                             Yield y s' -> Yield x (Just y, s')
                             Skip    s' -> Skip    (Just x, s')
                             Done       -> Done
                         ) (step s)

-- | All but the first element
tail :: Monad m => Stream m a -> Stream m a
{-# INLINE_STREAM tail #-}
tail (Stream step s sz) = Stream step' (Left s) (sz - 1)
  where
    {-# INLINE_INNER step' #-}
    step' (Left  s) = liftM (\r ->
                        case r of
                          Yield x s' -> Skip (Right s')
                          Skip    s' -> Skip (Left  s')
                          Done       -> EMPTY_STREAM "tail"
                      ) (step s)

    step' (Right s) = liftM (\r ->
                        case r of
                          Yield x s' -> Yield x (Right s')
                          Skip    s' -> Skip    (Right s')
                          Done       -> Done
                      ) (step s)

-- | The first @n@ elements
take :: Monad m => Int -> Stream m a -> Stream m a
{-# INLINE_STREAM take #-}
take n (Stream step s sz) = Stream step' (s, 0) (smaller (Exact n) sz)
  where
    {-# INLINE_INNER step' #-}
    step' (s, i) | i < n = liftM (\r ->
                             case r of
                               Yield x s' -> Yield x (s', i+1)
                               Skip    s' -> Skip    (s', i)
                               Done       -> Done
                           ) (step s)
    step' (s, i) = return Done

-- | All but the first @n@ elements
drop :: Monad m => Int -> Stream m a -> Stream m a
{-# INLINE_STREAM drop #-}
drop n (Stream step s sz) = Stream step' (s, Just n) (sz - Exact n)
  where
    {-# INLINE_INNER step' #-}
    step' (s, Just i) | i > 0 = liftM (\r ->
                                case r of
                                   Yield x s' -> Skip (s', Just (i-1))
                                   Skip    s' -> Skip (s', Just i)
                                   Done       -> Done
                                ) (step s)
                      | otherwise = return $ Skip (s, Nothing)

    step' (s, Nothing) = liftM (\r ->
                           case r of
                             Yield x s' -> Yield x (s', Nothing)
                             Skip    s' -> Skip    (s', Nothing)
                             Done       -> Done
                           ) (step s)
                     
-- Mapping
-- -------

instance Monad m => Functor (Stream m) where
  {-# INLINE fmap #-}
  fmap = map

-- | Map a function over a 'Stream'
map :: Monad m => (a -> b) -> Stream m a -> Stream m b
{-# INLINE map #-}
map f = mapM (return . f)


-- | Map a monadic function over a 'Stream'
mapM :: Monad m => (a -> m b) -> Stream m a -> Stream m b
{-# INLINE_STREAM mapM #-}
mapM f (Stream step s n) = Stream step' s n
  where
    {-# INLINE_INNER step' #-}
    step' s = do
                r <- step s
                case r of
                  Yield x s' -> liftM  (`Yield` s') (f x)
                  Skip    s' -> return (Skip    s')
                  Done       -> return Done

consume :: Monad m => Stream m a -> m ()
{-# INLINE_STREAM consume #-}
consume (Stream step s _) = consume_loop SPEC s
  where
    consume_loop !sPEC s
      = do
          r <- step s
          case r of
            Yield _ s' -> consume_loop SPEC s'
            Skip    s' -> consume_loop SPEC s'
            Done       -> return ()

-- | Execute a monadic action for each element of the 'Stream'
mapM_ :: Monad m => (a -> m b) -> Stream m a -> m ()
{-# INLINE_STREAM mapM_ #-}
mapM_ m = consume . mapM m

-- | Transform a 'Stream' to use a different monad
trans :: (Monad m, Monad m') => (forall a. m a -> m' a)
                             -> Stream m a -> Stream m' a
{-# INLINE_STREAM trans #-}
trans f (Stream step s n) = Stream (f . step) s n

unbox :: Monad m => Stream m (Box a) -> Stream m a
{-# INLINE_STREAM unbox #-}
unbox (Stream step s n) = Stream step' s n
  where
    {-# INLINE_INNER step' #-}
    step' s = do
                r <- step s
                case r of
                  Yield (Box x) s' -> return $ Yield x s'
                  Skip          s' -> return $ Skip    s'
                  Done             -> return $ Done

-- Zipping
-- -------

-- | Pair each element in a 'Stream' with its index
indexed :: Monad m => Stream m a -> Stream m (Int,a)
{-# INLINE_STREAM indexed #-}
indexed (Stream step s n) = Stream step' (s,0) n
  where
    {-# INLINE_INNER step' #-}
    step' (s,i) = i `seq`
                  do
                    r <- step s
                    case r of
                      Yield x s' -> return $ Yield (i,x) (s', i+1)
                      Skip    s' -> return $ Skip        (s', i)
                      Done       -> return Done

-- | Pair each element in a 'Stream' with its index, starting from the right
-- and counting down
indexedR :: Monad m => Int -> Stream m a -> Stream m (Int,a)
{-# INLINE_STREAM indexedR #-}
indexedR m (Stream step s n) = Stream step' (s,m) n
  where
    {-# INLINE_INNER step' #-}
    step' (s,i) = i `seq`
                  do
                    r <- step s
                    case r of
                      Yield x s' -> let i' = i-1
                                    in
                                    return $ Yield (i',x) (s', i')
                      Skip    s' -> return $ Skip         (s', i)
                      Done       -> return Done

-- | Zip two 'Stream's with the given monadic function
zipWithM :: Monad m => (a -> b -> m c) -> Stream m a -> Stream m b -> Stream m c
{-# INLINE_STREAM zipWithM #-}
zipWithM f (Stream stepa sa na) (Stream stepb sb nb)
  = Stream step (sa, sb, Nothing) (smaller na nb)
  where
    {-# INLINE_INNER step #-}
    step (sa, sb, Nothing) = liftM (\r ->
                               case r of
                                 Yield x sa' -> Skip (sa', sb, Just x)
                                 Skip    sa' -> Skip (sa', sb, Nothing)
                                 Done        -> Done
                             ) (stepa sa)

    step (sa, sb, Just x)  = do
                               r <- stepb sb
                               case r of
                                 Yield y sb' ->
                                   do
                                     z <- f x y
                                     return $ Yield z (sa, sb', Nothing)
                                 Skip    sb' -> return $ Skip (sa, sb', Just x)
                                 Done        -> return $ Done

-- FIXME: This might expose an opportunity for inplace execution.
{-# RULES

"zipWithM xs xs [Vector.Stream]" forall f xs.
  zipWithM f xs xs = mapM (\x -> f x x) xs

  #-}

zipWithM_ :: Monad m => (a -> b -> m c) -> Stream m a -> Stream m b -> m ()
{-# INLINE zipWithM_ #-}
zipWithM_ f sa sb = consume (zipWithM f sa sb)

zipWith3M :: Monad m => (a -> b -> c -> m d) -> Stream m a -> Stream m b -> Stream m c -> Stream m d
{-# INLINE_STREAM zipWith3M #-}
zipWith3M f (Stream stepa sa na) (Stream stepb sb nb) (Stream stepc sc nc)
  = Stream step (sa, sb, sc, Nothing) (smaller na (smaller nb nc))
  where
    {-# INLINE_INNER step #-}
    step (sa, sb, sc, Nothing) = do
        r <- stepa sa
        return $ case r of
            Yield x sa' -> Skip (sa', sb, sc, Just (x, Nothing))
            Skip    sa' -> Skip (sa', sb, sc, Nothing)
            Done        -> Done

    step (sa, sb, sc, Just (x, Nothing)) = do
        r <- stepb sb
        return $ case r of
            Yield y sb' -> Skip (sa, sb', sc, Just (x, Just y))
            Skip    sb' -> Skip (sa, sb', sc, Just (x, Nothing))
            Done        -> Done

    step (sa, sb, sc, Just (x, Just y)) = do
        r <- stepc sc
        case r of
            Yield z sc' -> f x y z >>= (\res -> return $ Yield res (sa, sb, sc', Nothing))
            Skip    sc' -> return $ Skip (sa, sb, sc', Just (x, Just y))
            Done        -> return $ Done

zipWith4M :: Monad m => (a -> b -> c -> d -> m e)
                     -> Stream m a -> Stream m b -> Stream m c -> Stream m d
                     -> Stream m e
{-# INLINE zipWith4M #-}
zipWith4M f sa sb sc sd
  = zipWithM (\(a,b) (c,d) -> f a b c d) (zip sa sb) (zip sc sd)

zipWith5M :: Monad m => (a -> b -> c -> d -> e -> m f)
                     -> Stream m a -> Stream m b -> Stream m c -> Stream m d
                     -> Stream m e -> Stream m f
{-# INLINE zipWith5M #-}
zipWith5M f sa sb sc sd se
  = zipWithM (\(a,b,c) (d,e) -> f a b c d e) (zip3 sa sb sc) (zip sd se)

zipWith6M :: Monad m => (a -> b -> c -> d -> e -> f -> m g)
                     -> Stream m a -> Stream m b -> Stream m c -> Stream m d
                     -> Stream m e -> Stream m f -> Stream m g
{-# INLINE zipWith6M #-}
zipWith6M fn sa sb sc sd se sf
  = zipWithM (\(a,b,c) (d,e,f) -> fn a b c d e f) (zip3 sa sb sc)
                                                  (zip3 sd se sf)

zipWith :: Monad m => (a -> b -> c) -> Stream m a -> Stream m b -> Stream m c
{-# INLINE zipWith #-}
zipWith f = zipWithM (\a b -> return (f a b))

zipWith3 :: Monad m => (a -> b -> c -> d)
                    -> Stream m a -> Stream m b -> Stream m c -> Stream m d
{-# INLINE zipWith3 #-}
zipWith3 f = zipWith3M (\a b c -> return (f a b c))

zipWith4 :: Monad m => (a -> b -> c -> d -> e)
                    -> Stream m a -> Stream m b -> Stream m c -> Stream m d
                    -> Stream m e
{-# INLINE zipWith4 #-}
zipWith4 f = zipWith4M (\a b c d -> return (f a b c d))

zipWith5 :: Monad m => (a -> b -> c -> d -> e -> f)
                    -> Stream m a -> Stream m b -> Stream m c -> Stream m d
                    -> Stream m e -> Stream m f
{-# INLINE zipWith5 #-}
zipWith5 f = zipWith5M (\a b c d e -> return (f a b c d e))

zipWith6 :: Monad m => (a -> b -> c -> d -> e -> f -> g)
                    -> Stream m a -> Stream m b -> Stream m c -> Stream m d
                    -> Stream m e -> Stream m f -> Stream m g
{-# INLINE zipWith6 #-}
zipWith6 fn = zipWith6M (\a b c d e f -> return (fn a b c d e f))

zip :: Monad m => Stream m a -> Stream m b -> Stream m (a,b)
{-# INLINE zip #-}
zip = zipWith (,)

zip3 :: Monad m => Stream m a -> Stream m b -> Stream m c -> Stream m (a,b,c)
{-# INLINE zip3 #-}
zip3 = zipWith3 (,,)

zip4 :: Monad m => Stream m a -> Stream m b -> Stream m c -> Stream m d
                -> Stream m (a,b,c,d)
{-# INLINE zip4 #-}
zip4 = zipWith4 (,,,)

zip5 :: Monad m => Stream m a -> Stream m b -> Stream m c -> Stream m d
                -> Stream m e -> Stream m (a,b,c,d,e)
{-# INLINE zip5 #-}
zip5 = zipWith5 (,,,,)

zip6 :: Monad m => Stream m a -> Stream m b -> Stream m c -> Stream m d
                -> Stream m e -> Stream m f -> Stream m (a,b,c,d,e,f)
{-# INLINE zip6 #-}
zip6 = zipWith6 (,,,,,)

-- Filtering
-- ---------

-- | Drop elements which do not satisfy the predicate
filter :: Monad m => (a -> Bool) -> Stream m a -> Stream m a
{-# INLINE filter #-}
filter f = filterM (return . f)

-- | Drop elements which do not satisfy the monadic predicate
filterM :: Monad m => (a -> m Bool) -> Stream m a -> Stream m a
{-# INLINE_STREAM filterM #-}
filterM f (Stream step s n) = Stream step' s (toMax n)
  where
    {-# INLINE_INNER step' #-}
    step' s = do
                r <- step s
                case r of
                  Yield x s' -> do
                                  b <- f x
                                  return $ if b then Yield x s'
                                                else Skip    s'
                  Skip    s' -> return $ Skip s'
                  Done       -> return $ Done

-- | Longest prefix of elements that satisfy the predicate
takeWhile :: Monad m => (a -> Bool) -> Stream m a -> Stream m a
{-# INLINE takeWhile #-}
takeWhile f = takeWhileM (return . f)

-- | Longest prefix of elements that satisfy the monadic predicate
takeWhileM :: Monad m => (a -> m Bool) -> Stream m a -> Stream m a
{-# INLINE_STREAM takeWhileM #-}
takeWhileM f (Stream step s n) = Stream step' s (toMax n)
  where
    {-# INLINE_INNER step' #-}
    step' s = do
                r <- step s
                case r of
                  Yield x s' -> do
                                  b <- f x
                                  return $ if b then Yield x s' else Done
                  Skip    s' -> return $ Skip s'
                  Done       -> return $ Done

-- | Drop the longest prefix of elements that satisfy the predicate
dropWhile :: Monad m => (a -> Bool) -> Stream m a -> Stream m a
{-# INLINE dropWhile #-}
dropWhile f = dropWhileM (return . f)

data DropWhile s a = DropWhile_Drop s | DropWhile_Yield a s | DropWhile_Next s

-- | Drop the longest prefix of elements that satisfy the monadic predicate
dropWhileM :: Monad m => (a -> m Bool) -> Stream m a -> Stream m a
{-# INLINE_STREAM dropWhileM #-}
dropWhileM f (Stream step s n) = Stream step' (DropWhile_Drop s) (toMax n)
  where
    -- NOTE: we jump through hoops here to have only one Yield; local data
    -- declarations would be nice!

    {-# INLINE_INNER step' #-}
    step' (DropWhile_Drop s)
      = do
          r <- step s
          case r of
            Yield x s' -> do
                            b <- f x
                            return $ if b then Skip (DropWhile_Drop    s')
                                          else Skip (DropWhile_Yield x s')
            Skip    s' -> return $ Skip (DropWhile_Drop    s')
            Done       -> return $ Done

    step' (DropWhile_Yield x s) = return $ Yield x (DropWhile_Next s)

    step' (DropWhile_Next s)
      = liftM (\r ->
          case r of
            Yield x s' -> Skip    (DropWhile_Yield x s')
            Skip    s' -> Skip    (DropWhile_Next    s')
            Done       -> Done
        ) (step s)

-- Searching
-- ---------

infix 4 `elem`
-- | Check whether the 'Stream' contains an element
elem :: (Monad m, Eq a) => a -> Stream m a -> m Bool
{-# INLINE_STREAM elem #-}
elem x (Stream step s _) = elem_loop SPEC s
  where
    elem_loop !sPEC s
      = do
          r <- step s
          case r of
            Yield y s' | x == y    -> return True
                       | otherwise -> elem_loop SPEC s'
            Skip    s'             -> elem_loop SPEC s'
            Done                   -> return False

infix 4 `notElem`
-- | Inverse of `elem`
notElem :: (Monad m, Eq a) => a -> Stream m a -> m Bool
{-# INLINE notElem #-}
notElem x s = liftM not (elem x s)

-- | Yield 'Just' the first element that satisfies the predicate or 'Nothing'
-- if no such element exists.
find :: Monad m => (a -> Bool) -> Stream m a -> m (Maybe a)
{-# INLINE find #-}
find f = findM (return . f)

-- | Yield 'Just' the first element that satisfies the monadic predicate or
-- 'Nothing' if no such element exists.
findM :: Monad m => (a -> m Bool) -> Stream m a -> m (Maybe a)
{-# INLINE_STREAM findM #-}
findM f (Stream step s _) = find_loop SPEC s
  where
    find_loop !sPEC s
      = do
          r <- step s
          case r of
            Yield x s' -> do
                            b <- f x
                            if b then return $ Just x
                                 else find_loop SPEC s'
            Skip    s' -> find_loop SPEC s'
            Done       -> return Nothing

-- | Yield 'Just' the index of the first element that satisfies the predicate
-- or 'Nothing' if no such element exists.
findIndex :: Monad m => (a -> Bool) -> Stream m a -> m (Maybe Int)
{-# INLINE_STREAM findIndex #-}
findIndex f = findIndexM (return . f)

-- | Yield 'Just' the index of the first element that satisfies the monadic
-- predicate or 'Nothing' if no such element exists.
findIndexM :: Monad m => (a -> m Bool) -> Stream m a -> m (Maybe Int)
{-# INLINE_STREAM findIndexM #-}
findIndexM f (Stream step s _) = findIndex_loop SPEC s 0
  where
    findIndex_loop !sPEC s i
      = do
          r <- step s
          case r of
            Yield x s' -> do
                            b <- f x
                            if b then return $ Just i
                                 else findIndex_loop SPEC s' (i+1)
            Skip    s' -> findIndex_loop SPEC s' i
            Done       -> return Nothing

-- Folding
-- -------

-- | Left fold
foldl :: Monad m => (a -> b -> a) -> a -> Stream m b -> m a
{-# INLINE foldl #-}
foldl f = foldlM (\a b -> return (f a b))

-- | Left fold with a monadic operator
foldlM :: Monad m => (a -> b -> m a) -> a -> Stream m b -> m a
{-# INLINE_STREAM foldlM #-}
foldlM m z (Stream step s _) = foldlM_loop SPEC z s
  where
    foldlM_loop !sPEC z s
      = do
          r <- step s
          case r of
            Yield x s' -> do { z' <- m z x; foldlM_loop SPEC z' s' }
            Skip    s' -> foldlM_loop SPEC z s'
            Done       -> return z

-- | Same as 'foldlM'
foldM :: Monad m => (a -> b -> m a) -> a -> Stream m b -> m a
{-# INLINE foldM #-}
foldM = foldlM

-- | Left fold over a non-empty 'Stream'
foldl1 :: Monad m => (a -> a -> a) -> Stream m a -> m a
{-# INLINE foldl1 #-}
foldl1 f = foldl1M (\a b -> return (f a b))

-- | Left fold over a non-empty 'Stream' with a monadic operator
foldl1M :: Monad m => (a -> a -> m a) -> Stream m a -> m a
{-# INLINE_STREAM foldl1M #-}
foldl1M f (Stream step s sz) = foldl1M_loop SPEC s
  where
    foldl1M_loop !sPEC s
      = do
          r <- step s
          case r of
            Yield x s' -> foldlM f x (Stream step s' (sz - 1))
            Skip    s' -> foldl1M_loop SPEC s'
            Done       -> EMPTY_STREAM "foldl1M"

-- | Same as 'foldl1M'
fold1M :: Monad m => (a -> a -> m a) -> Stream m a -> m a
{-# INLINE fold1M #-}
fold1M = foldl1M

-- | Left fold with a strict accumulator
foldl' :: Monad m => (a -> b -> a) -> a -> Stream m b -> m a
{-# INLINE foldl' #-}
foldl' f = foldlM' (\a b -> return (f a b))

-- | Left fold with a strict accumulator and a monadic operator
foldlM' :: Monad m => (a -> b -> m a) -> a -> Stream m b -> m a
{-# INLINE_STREAM foldlM' #-}
foldlM' m z (Stream step s _) = foldlM'_loop SPEC z s
  where
    foldlM'_loop !sPEC z s
      = z `seq`
        do
          r <- step s
          case r of
            Yield x s' -> do { z' <- m z x; foldlM'_loop SPEC z' s' }
            Skip    s' -> foldlM'_loop SPEC z s'
            Done       -> return z

-- | Same as 'foldlM''
foldM' :: Monad m => (a -> b -> m a) -> a -> Stream m b -> m a
{-# INLINE foldM' #-}
foldM' = foldlM'

-- | Left fold over a non-empty 'Stream' with a strict accumulator
foldl1' :: Monad m => (a -> a -> a) -> Stream m a -> m a
{-# INLINE foldl1' #-}
foldl1' f = foldl1M' (\a b -> return (f a b))

-- | Left fold over a non-empty 'Stream' with a strict accumulator and a
-- monadic operator
foldl1M' :: Monad m => (a -> a -> m a) -> Stream m a -> m a
{-# INLINE_STREAM foldl1M' #-}
foldl1M' f (Stream step s sz) = foldl1M'_loop SPEC s
  where
    foldl1M'_loop !sPEC s
      = do
          r <- step s
          case r of
            Yield x s' -> foldlM' f x (Stream step s' (sz - 1))
            Skip    s' -> foldl1M'_loop SPEC s'
            Done       -> EMPTY_STREAM "foldl1M'"

-- | Same as 'foldl1M''
fold1M' :: Monad m => (a -> a -> m a) -> Stream m a -> m a
{-# INLINE fold1M' #-}
fold1M' = foldl1M'

-- | Right fold
foldr :: Monad m => (a -> b -> b) -> b -> Stream m a -> m b
{-# INLINE foldr #-}
foldr f = foldrM (\a b -> return (f a b))

-- | Right fold with a monadic operator
foldrM :: Monad m => (a -> b -> m b) -> b -> Stream m a -> m b
{-# INLINE_STREAM foldrM #-}
foldrM f z (Stream step s _) = foldrM_loop SPEC s
  where
    foldrM_loop !sPEC s
      = do
          r <- step s
          case r of
            Yield x s' -> f x =<< foldrM_loop SPEC s'
            Skip    s' -> foldrM_loop SPEC s'
            Done       -> return z

-- | Right fold over a non-empty stream
foldr1 :: Monad m => (a -> a -> a) -> Stream m a -> m a
{-# INLINE foldr1 #-}
foldr1 f = foldr1M (\a b -> return (f a b))

-- | Right fold over a non-empty stream with a monadic operator
foldr1M :: Monad m => (a -> a -> m a) -> Stream m a -> m a
{-# INLINE_STREAM foldr1M #-}
foldr1M f (Stream step s _) = foldr1M_loop0 SPEC s
  where
    foldr1M_loop0 !sPEC s
      = do
          r <- step s
          case r of
            Yield x s' -> foldr1M_loop1 SPEC x s'
            Skip    s' -> foldr1M_loop0 SPEC   s'
            Done       -> EMPTY_STREAM "foldr1M"

    foldr1M_loop1 !sPEC x s
      = do
          r <- step s
          case r of
            Yield y s' -> f x =<< foldr1M_loop1 SPEC y s'
            Skip    s' -> foldr1M_loop1 SPEC x s'
            Done       -> return x

-- Specialised folds
-- -----------------

and :: Monad m => Stream m Bool -> m Bool
{-# INLINE_STREAM and #-}
and (Stream step s _) = and_loop SPEC s
  where
    and_loop !sPEC s
      = do
          r <- step s
          case r of
            Yield False _  -> return False
            Yield True  s' -> and_loop SPEC s'
            Skip        s' -> and_loop SPEC s'
            Done           -> return True

or :: Monad m => Stream m Bool -> m Bool
{-# INLINE_STREAM or #-}
or (Stream step s _) = or_loop SPEC s
  where
    or_loop !sPEC s
      = do
          r <- step s
          case r of
            Yield False s' -> or_loop SPEC s'
            Yield True  _  -> return True
            Skip        s' -> or_loop SPEC s'
            Done           -> return False

concatMap :: Monad m => (a -> Stream m b) -> Stream m a -> Stream m b
{-# INLINE concatMap #-}
concatMap f = concatMapM (return . f)

concatMapM :: Monad m => (a -> m (Stream m b)) -> Stream m a -> Stream m b
{-# INLINE_STREAM concatMapM #-}
concatMapM f (Stream step s _) = Stream concatMap_go (Left s) Unknown
  where
    concatMap_go (Left s) = do
        r <- step s
        case r of
            Yield a s' -> do
                b_stream <- f a
                return $ Skip (Right (b_stream, s'))
            Skip    s' -> return $ Skip (Left s')
            Done       -> return Done
    concatMap_go (Right (Stream inner_step inner_s sz, s)) = do
        r <- inner_step inner_s
        case r of
            Yield b inner_s' -> return $ Yield b (Right (Stream inner_step inner_s' sz, s))
            Skip    inner_s' -> return $ Skip (Right (Stream inner_step inner_s' sz, s))
            Done             -> return $ Skip (Left s)

-- | Create a 'Stream' of values from a 'Stream' of streamable things
flatten :: Monad m => (a -> m s) -> (s -> m (Step s b)) -> Size
                   -> Stream m a -> Stream m b
{-# INLINE_STREAM flatten #-}
flatten mk istep sz (Stream ostep t _) = Stream step (Left t) sz
  where
    {-# INLINE_INNER step #-}
    step (Left t) = do
                      r <- ostep t
                      case r of
                        Yield a t' -> do
                                        s <- mk a
                                        s `seq` return (Skip (Right (s,t')))
                        Skip    t' -> return $ Skip (Left t')
                        Done       -> return $ Done

    
    step (Right (s,t)) = do
                           r <- istep s
                           case r of
                             Yield x s' -> return $ Yield x (Right (s',t))
                             Skip    s' -> return $ Skip    (Right (s',t))
                             Done       -> return $ Skip    (Left t)

-- Unfolding
-- ---------

-- | Unfold
unfoldr :: Monad m => (s -> Maybe (a, s)) -> s -> Stream m a
{-# INLINE_STREAM unfoldr #-}
unfoldr f = unfoldrM (return . f)

-- | Unfold with a monadic function
unfoldrM :: Monad m => (s -> m (Maybe (a, s))) -> s -> Stream m a
{-# INLINE_STREAM unfoldrM #-}
unfoldrM f s = Stream step s Unknown
  where
    {-# INLINE_INNER step #-}
    step s = liftM (\r ->
               case r of
                 Just (x, s') -> Yield x s'
                 Nothing      -> Done
             ) (f s)

-- | Unfold at most @n@ elements
unfoldrN :: Monad m => Int -> (s -> Maybe (a, s)) -> s -> Stream m a
{-# INLINE_STREAM unfoldrN #-}
unfoldrN n f = unfoldrNM n (return . f)

-- | Unfold at most @n@ elements with a monadic functions
unfoldrNM :: Monad m => Int -> (s -> m (Maybe (a, s))) -> s -> Stream m a
{-# INLINE_STREAM unfoldrNM #-}
unfoldrNM n f s = Stream step (s,n) (Max (delay_inline max n 0))
  where
    {-# INLINE_INNER step #-}
    step (s,n) | n <= 0    = return Done
               | otherwise = liftM (\r ->
                               case r of
                                 Just (x,s') -> Yield x (s',n-1)
                                 Nothing     -> Done
                             ) (f s)

-- | Apply monadic function n times to value. Zeroth element is original value.
iterateNM :: Monad m => Int -> (a -> m a) -> a -> Stream m a
{-# INLINE_STREAM iterateNM #-}
iterateNM n f x0 = Stream step (x0,n) (Exact (delay_inline max n 0))
  where
    {-# INLINE_INNER step #-}
    step (x,i) | i <= 0    = return Done
               | i == n    = return $ Yield x (x,i-1)
               | otherwise = do a <- f x
                                return $ Yield a (a,i-1)

-- | Apply function n times to value. Zeroth element is original value.
iterateN :: Monad m => Int -> (a -> a) -> a -> Stream m a
{-# INLINE_STREAM iterateN #-}
iterateN n f x0 = iterateNM n (return . f) x0

-- Scans
-- -----

-- | Prefix scan
prescanl :: Monad m => (a -> b -> a) -> a -> Stream m b -> Stream m a
{-# INLINE prescanl #-}
prescanl f = prescanlM (\a b -> return (f a b))

-- | Prefix scan with a monadic operator
prescanlM :: Monad m => (a -> b -> m a) -> a -> Stream m b -> Stream m a
{-# INLINE_STREAM prescanlM #-}
prescanlM f z (Stream step s sz) = Stream step' (s,z) sz
  where
    {-# INLINE_INNER step' #-}
    step' (s,x) = do
                    r <- step s
                    case r of
                      Yield y s' -> do
                                      z <- f x y
                                      return $ Yield x (s', z)
                      Skip    s' -> return $ Skip (s', x)
                      Done       -> return Done

-- | Prefix scan with strict accumulator
prescanl' :: Monad m => (a -> b -> a) -> a -> Stream m b -> Stream m a
{-# INLINE prescanl' #-}
prescanl' f = prescanlM' (\a b -> return (f a b))

-- | Prefix scan with strict accumulator and a monadic operator
prescanlM' :: Monad m => (a -> b -> m a) -> a -> Stream m b -> Stream m a
{-# INLINE_STREAM prescanlM' #-}
prescanlM' f z (Stream step s sz) = Stream step' (s,z) sz
  where
    {-# INLINE_INNER step' #-}
    step' (s,x) = x `seq`
                  do
                    r <- step s
                    case r of
                      Yield y s' -> do
                                      z <- f x y
                                      return $ Yield x (s', z)
                      Skip    s' -> return $ Skip (s', x)
                      Done       -> return Done

-- | Suffix scan
postscanl :: Monad m => (a -> b -> a) -> a -> Stream m b -> Stream m a
{-# INLINE postscanl #-}
postscanl f = postscanlM (\a b -> return (f a b))

-- | Suffix scan with a monadic operator
postscanlM :: Monad m => (a -> b -> m a) -> a -> Stream m b -> Stream m a
{-# INLINE_STREAM postscanlM #-}
postscanlM f z (Stream step s sz) = Stream step' (s,z) sz
  where
    {-# INLINE_INNER step' #-}
    step' (s,x) = do
                    r <- step s
                    case r of
                      Yield y s' -> do
                                      z <- f x y
                                      return $ Yield z (s',z)
                      Skip    s' -> return $ Skip (s',x)
                      Done       -> return Done

-- | Suffix scan with strict accumulator
postscanl' :: Monad m => (a -> b -> a) -> a -> Stream m b -> Stream m a
{-# INLINE postscanl' #-}
postscanl' f = postscanlM' (\a b -> return (f a b))

-- | Suffix scan with strict acccumulator and a monadic operator
postscanlM' :: Monad m => (a -> b -> m a) -> a -> Stream m b -> Stream m a
{-# INLINE_STREAM postscanlM' #-}
postscanlM' f z (Stream step s sz) = z `seq` Stream step' (s,z) sz
  where
    {-# INLINE_INNER step' #-}
    step' (s,x) = x `seq`
                  do
                    r <- step s
                    case r of
                      Yield y s' -> do
                                      z <- f x y
                                      z `seq` return (Yield z (s',z))
                      Skip    s' -> return $ Skip (s',x)
                      Done       -> return Done

-- | Haskell-style scan
scanl :: Monad m => (a -> b -> a) -> a -> Stream m b -> Stream m a
{-# INLINE scanl #-}
scanl f = scanlM (\a b -> return (f a b))

-- | Haskell-style scan with a monadic operator
scanlM :: Monad m => (a -> b -> m a) -> a -> Stream m b -> Stream m a
{-# INLINE scanlM #-}
scanlM f z s = z `cons` postscanlM f z s

-- | Haskell-style scan with strict accumulator
scanl' :: Monad m => (a -> b -> a) -> a -> Stream m b -> Stream m a
{-# INLINE scanl' #-}
scanl' f = scanlM' (\a b -> return (f a b))

-- | Haskell-style scan with strict accumulator and a monadic operator
scanlM' :: Monad m => (a -> b -> m a) -> a -> Stream m b -> Stream m a
{-# INLINE scanlM' #-}
scanlM' f z s = z `seq` (z `cons` postscanlM f z s)

-- | Scan over a non-empty 'Stream'
scanl1 :: Monad m => (a -> a -> a) -> Stream m a -> Stream m a
{-# INLINE scanl1 #-}
scanl1 f = scanl1M (\x y -> return (f x y))

-- | Scan over a non-empty 'Stream' with a monadic operator
scanl1M :: Monad m => (a -> a -> m a) -> Stream m a -> Stream m a
{-# INLINE_STREAM scanl1M #-}
scanl1M f (Stream step s sz) = Stream step' (s, Nothing) sz
  where
    {-# INLINE_INNER step' #-}
    step' (s, Nothing) = do
                           r <- step s
                           case r of
                             Yield x s' -> return $ Yield x (s', Just x)
                             Skip    s' -> return $ Skip (s', Nothing)
                             Done       -> EMPTY_STREAM "scanl1M"

    step' (s, Just x) = do
                          r <- step s
                          case r of
                            Yield y s' -> do
                                            z <- f x y
                                            return $ Yield z (s', Just z)
                            Skip    s' -> return $ Skip (s', Just x)
                            Done       -> return Done

-- | Scan over a non-empty 'Stream' with a strict accumulator
scanl1' :: Monad m => (a -> a -> a) -> Stream m a -> Stream m a
{-# INLINE scanl1' #-}
scanl1' f = scanl1M' (\x y -> return (f x y))

-- | Scan over a non-empty 'Stream' with a strict accumulator and a monadic
-- operator
scanl1M' :: Monad m => (a -> a -> m a) -> Stream m a -> Stream m a
{-# INLINE_STREAM scanl1M' #-}
scanl1M' f (Stream step s sz) = Stream step' (s, Nothing) sz
  where
    {-# INLINE_INNER step' #-}
    step' (s, Nothing) = do
                           r <- step s
                           case r of
                             Yield x s' -> x `seq` return (Yield x (s', Just x))
                             Skip    s' -> return $ Skip (s', Nothing)
                             Done       -> EMPTY_STREAM "scanl1M"

    step' (s, Just x) = x `seq`
                        do
                          r <- step s
                          case r of
                            Yield y s' -> do
                                            z <- f x y
                                            z `seq` return (Yield z (s', Just z))
                            Skip    s' -> return $ Skip (s', Just x)
                            Done       -> return Done

-- Enumerations
-- ------------

-- The Enum class is broken for this, there just doesn't seem to be a
-- way to implement this generically. We have to specialise for as many types
-- as we can but this doesn't help in polymorphic loops.

-- | Yield a 'Stream' of the given length containing the values @x@, @x+y@,
-- @x+y+y@ etc.
enumFromStepN :: (Num a, Monad m) => a -> a -> Int -> Stream m a
{-# INLINE_STREAM enumFromStepN #-}
enumFromStepN x y n = x `seq` y `seq` n `seq`
                      Stream step (x,n) (Exact (delay_inline max n 0))
  where
    {-# INLINE_INNER step #-}
    step (x,n) | n > 0     = return $ Yield x (x+y,n-1)
               | otherwise = return $ Done

-- | Enumerate values
--
-- /WARNING:/ This operation can be very inefficient. If at all possible, use
-- 'enumFromStepN' instead.
enumFromTo :: (Enum a, Monad m) => a -> a -> Stream m a
{-# INLINE_STREAM enumFromTo #-}
enumFromTo x y = fromList [x .. y]

-- NOTE: We use (x+1) instead of (succ x) below because the latter checks for
-- overflow which can't happen here.

-- FIXME: add "too large" test for Int
enumFromTo_small :: (Integral a, Monad m) => a -> a -> Stream m a
{-# INLINE_STREAM enumFromTo_small #-}
enumFromTo_small x y = x `seq` y `seq` Stream step x (Exact n)
  where
    n = delay_inline max (fromIntegral y - fromIntegral x + 1) 0

    {-# INLINE_INNER step #-}
    step x | x <= y    = return $ Yield x (x+1)
           | otherwise = return $ Done

{-# RULES

"enumFromTo<Int8> [Stream]"
  enumFromTo = enumFromTo_small :: Monad m => Int8 -> Int8 -> Stream m Int8

"enumFromTo<Int16> [Stream]"
  enumFromTo = enumFromTo_small :: Monad m => Int16 -> Int16 -> Stream m Int16

"enumFromTo<Word8> [Stream]"
  enumFromTo = enumFromTo_small :: Monad m => Word8 -> Word8 -> Stream m Word8

"enumFromTo<Word16> [Stream]"
  enumFromTo = enumFromTo_small :: Monad m => Word16 -> Word16 -> Stream m Word16

  #-}

#if WORD_SIZE_IN_BITS > 32

{-# RULES

"enumFromTo<Int32> [Stream]"
  enumFromTo = enumFromTo_small :: Monad m => Int32 -> Int32 -> Stream m Int32

"enumFromTo<Word32> [Stream]"
  enumFromTo = enumFromTo_small :: Monad m => Word32 -> Word32 -> Stream m Word32

  #-}

#endif

-- NOTE: We could implement a generic "too large" test:
--
-- len x y | x > y = 0
--         | n > 0 && n <= fromIntegral (maxBound :: Int) = fromIntegral n
--         | otherwise = error
--   where
--     n = y-x+1
--
-- Alas, GHC won't eliminate unnecessary comparisons (such as n >= 0 for
-- unsigned types). See http://hackage.haskell.org/trac/ghc/ticket/3744
--

enumFromTo_int :: (Integral a, Monad m) => a -> a -> Stream m a
{-# INLINE_STREAM enumFromTo_int #-}
enumFromTo_int x y = x `seq` y `seq` Stream step x (Exact (len x y))
  where
    {-# INLINE [0] len #-}
    len x y | x > y     = 0
            | otherwise = BOUNDS_CHECK(check) "enumFromTo" "vector too large"
                          (n > 0)
                        $ fromIntegral n
      where
        n = y-x+1

    {-# INLINE_INNER step #-}
    step x | x <= y    = return $ Yield x (x+1)
           | otherwise = return $ Done

{-# RULES

"enumFromTo<Int> [Stream]"
  enumFromTo = enumFromTo_int :: Monad m => Int -> Int -> Stream m Int

#if WORD_SIZE_IN_BITS > 32

"enumFromTo<Int64> [Stream]"
  enumFromTo = enumFromTo_int :: Monad m => Int64 -> Int64 -> Stream m Int64

#else

"enumFromTo<Int32> [Stream]"
  enumFromTo = enumFromTo_int :: Monad m => Int32 -> Int32 -> Stream m Int32

#endif

  #-}

enumFromTo_big_word :: (Integral a, Monad m) => a -> a -> Stream m a
{-# INLINE_STREAM enumFromTo_big_word #-}
enumFromTo_big_word x y = x `seq` y `seq` Stream step x (Exact (len x y))
  where
    {-# INLINE [0] len #-}
    len x y | x > y     = 0
            | otherwise = BOUNDS_CHECK(check) "enumFromTo" "vector too large"
                          (n < fromIntegral (maxBound :: Int))
                        $ fromIntegral (n+1)
      where
        n = y-x

    {-# INLINE_INNER step #-}
    step x | x <= y    = return $ Yield x (x+1)
           | otherwise = return $ Done

{-# RULES

"enumFromTo<Word> [Stream]"
  enumFromTo = enumFromTo_big_word :: Monad m => Word -> Word -> Stream m Word

"enumFromTo<Word64> [Stream]"
  enumFromTo = enumFromTo_big_word
                        :: Monad m => Word64 -> Word64 -> Stream m Word64

#if WORD_SIZE_IN_BITS == 32

"enumFromTo<Word32> [Stream]"
  enumFromTo = enumFromTo_big_word
                        :: Monad m => Word32 -> Word32 -> Stream m Word32

#endif

"enumFromTo<Integer> [Stream]"
  enumFromTo = enumFromTo_big_word
                        :: Monad m => Integer -> Integer -> Stream m Integer

  #-}

-- FIXME: the "too large" test is totally wrong
enumFromTo_big_int :: (Integral a, Monad m) => a -> a -> Stream m a
{-# INLINE_STREAM enumFromTo_big_int #-}
enumFromTo_big_int x y = x `seq` y `seq` Stream step x (Exact (len x y))
  where
    {-# INLINE [0] len #-}
    len x y | x > y     = 0
            | otherwise = BOUNDS_CHECK(check) "enumFromTo" "vector too large"
                          (n > 0 && n <= fromIntegral (maxBound :: Int))
                        $ fromIntegral n
      where
        n = y-x+1

    {-# INLINE_INNER step #-}
    step x | x <= y    = return $ Yield x (x+1)
           | otherwise = return $ Done

#if WORD_SIZE_IN_BITS > 32

{-# RULES

"enumFromTo<Int64> [Stream]"
  enumFromTo = enumFromTo_big :: Monad m => Int64 -> Int64 -> Stream m Int64

  #-}

#endif

enumFromTo_char :: Monad m => Char -> Char -> Stream m Char
{-# INLINE_STREAM enumFromTo_char #-}
enumFromTo_char x y = x `seq` y `seq` Stream step xn (Exact n)
  where
    xn = ord x
    yn = ord y

    n = delay_inline max 0 (yn - xn + 1)

    {-# INLINE_INNER step #-}
    step xn | xn <= yn  = return $ Yield (unsafeChr xn) (xn+1)
            | otherwise = return $ Done

{-# RULES

"enumFromTo<Char> [Stream]"
  enumFromTo = enumFromTo_char

  #-}

------------------------------------------------------------------------

-- Specialise enumFromTo for Float and Double.
-- Also, try to do something about pairs?

enumFromTo_double :: (Monad m, Ord a, RealFrac a) => a -> a -> Stream m a
{-# INLINE_STREAM enumFromTo_double #-}
enumFromTo_double n m = n `seq` m `seq` Stream step n (Max (len n m))
  where
    lim = m + 1/2 -- important to float out

    {-# INLINE [0] len #-}
    len x y | x > y     = 0
            | otherwise = BOUNDS_CHECK(check) "enumFromTo" "vector too large"
                          (n > 0)
                        $ fromIntegral n
      where
        n = truncate (y-x)+2

    {-# INLINE_INNER step #-}
    step x | x <= lim  = return $ Yield x (x+1)
           | otherwise = return $ Done

{-# RULES

"enumFromTo<Double> [Stream]"
  enumFromTo = enumFromTo_double :: Monad m => Double -> Double -> Stream m Double

"enumFromTo<Float> [Stream]"
  enumFromTo = enumFromTo_double :: Monad m => Float -> Float -> Stream m Float

  #-}

------------------------------------------------------------------------

-- | Enumerate values with a given step.
--
-- /WARNING:/ This operation is very inefficient. If at all possible, use
-- 'enumFromStepN' instead.
enumFromThenTo :: (Enum a, Monad m) => a -> a -> a -> Stream m a
{-# INLINE_STREAM enumFromThenTo #-}
enumFromThenTo x y z = fromList [x, y .. z]

-- FIXME: Specialise enumFromThenTo.

-- Conversions
-- -----------

-- | Convert a 'Stream' to a list
toList :: Monad m => Stream m a -> m [a]
{-# INLINE toList #-}
toList = foldr (:) []

-- | Convert a list to a 'Stream'
fromList :: Monad m => [a] -> Stream m a
{-# INLINE fromList #-}
fromList xs = unsafeFromList Unknown xs

-- | Convert the first @n@ elements of a list to a 'Stream'
fromListN :: Monad m => Int -> [a] -> Stream m a
{-# INLINE_STREAM fromListN #-}
fromListN n xs = Stream step (xs,n) (Max (delay_inline max n 0))
  where
    {-# INLINE_INNER step #-}
    step (xs,n) | n <= 0 = return Done
    step (x:xs,n)        = return (Yield x (xs,n-1))
    step ([],n)          = return Done

-- | Convert a list to a 'Stream' with the given 'Size' hint. 
unsafeFromList :: Monad m => Size -> [a] -> Stream m a
{-# INLINE_STREAM unsafeFromList #-}
unsafeFromList sz xs = Stream step xs sz
  where
    step (x:xs) = return (Yield x xs)
    step []     = return Done

