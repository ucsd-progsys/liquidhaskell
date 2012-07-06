{-# LANGUAGE CPP #-}
#if !defined(TESTING) && __GLASGOW_HASKELL__ >= 703
{-# LANGUAGE Trustworthy #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.IntMap.Strict
-- Copyright   :  (c) Daan Leijen 2002
--                (c) Andriy Palamarchuk 2008
-- License     :  BSD-style
-- Maintainer  :  libraries@haskell.org
-- Stability   :  provisional
-- Portability :  portable
--
-- An efficient implementation of maps from integer keys to values
-- (dictionaries).
--
-- API of this module is strict in both the keys and the values.
-- If you need value-lazy maps, use 'Data.IntMap.Lazy' instead.
-- The 'IntMap' type itself is shared between the lazy and strict modules,
-- meaning that the same 'IntMap' value can be passed to functions in
-- both modules (although that is rarely needed).
--
-- These modules are intended to be imported qualified, to avoid name
-- clashes with Prelude functions, e.g.
--
-- >  import Data.IntMap.Strict (IntMap)
-- >  import qualified Data.IntMap.Strict as IntMap
--
-- The implementation is based on /big-endian patricia trees/.  This data
-- structure performs especially well on binary operations like 'union'
-- and 'intersection'.  However, my benchmarks show that it is also
-- (much) faster on insertions and deletions when compared to a generic
-- size-balanced map implementation (see "Data.Map").
--
--    * Chris Okasaki and Andy Gill,  \"/Fast Mergeable Integer Maps/\",
--      Workshop on ML, September 1998, pages 77-86,
--      <http://citeseer.ist.psu.edu/okasaki98fast.html>
--
--    * D.R. Morrison, \"/PATRICIA -- Practical Algorithm To Retrieve
--      Information Coded In Alphanumeric/\", Journal of the ACM, 15(4),
--      October 1968, pages 514-534.
--
-- Operation comments contain the operation time complexity in
-- the Big-O notation <http://en.wikipedia.org/wiki/Big_O_notation>.
-- Many operations have a worst-case complexity of /O(min(n,W))/.
-- This means that the operation can become linear in the number of
-- elements with a maximum of /W/ -- the number of bits in an 'Int'
-- (32 or 64).
--
-- Be aware that the 'Functor', 'Traversable' and 'Data' instances
-- are the same as for the 'Data.IntMap.Lazy' module, so if they are used
-- on strict maps, the resulting maps will be lazy.
-----------------------------------------------------------------------------

-- See the notes at the beginning of Data.IntMap.Base.

module Data.IntMap.Strict (
            -- * Strictness properties
            -- $strictness

            -- * Map type
#if !defined(TESTING)
              IntMap, Key          -- instance Eq,Show
#else
              IntMap(..), Key          -- instance Eq,Show
#endif

            -- * Operators
            , (!), (\\)

            -- * Query
            , null
            , size
            , member
            , notMember
            , lookup
            , findWithDefault
            , lookupLT
            , lookupGT
            , lookupLE
            , lookupGE

            -- * Construction
            , empty
            , singleton

            -- ** Insertion
            , insert
            , insertWith
            , insertWithKey
            , insertLookupWithKey

            -- ** Delete\/Update
            , delete
            , adjust
            , adjustWithKey
            , update
            , updateWithKey
            , updateLookupWithKey
            , alter

            -- * Combine

            -- ** Union
            , union
            , unionWith
            , unionWithKey
            , unions
            , unionsWith

            -- ** Difference
            , difference
            , differenceWith
            , differenceWithKey

            -- ** Intersection
            , intersection
            , intersectionWith
            , intersectionWithKey

            -- ** Universal combining function
            , mergeWithKey

            -- * Traversal
            -- ** Map
            , map
            , mapWithKey
            , traverseWithKey
            , mapAccum
            , mapAccumWithKey
            , mapAccumRWithKey
            , mapKeys
            , mapKeysWith
            , mapKeysMonotonic

            -- * Folds
            , foldr
            , foldl
            , foldrWithKey
            , foldlWithKey
            -- ** Strict folds
            , foldr'
            , foldl'
            , foldrWithKey'
            , foldlWithKey'

            -- * Conversion
            , elems
            , keys
            , assocs
            , keysSet
            , fromSet

            -- ** Lists
            , toList
            , fromList
            , fromListWith
            , fromListWithKey

            -- ** Ordered lists
            , toAscList
            , toDescList
            , fromAscList
            , fromAscListWith
            , fromAscListWithKey
            , fromDistinctAscList

            -- * Filter
            , filter
            , filterWithKey
            , partition
            , partitionWithKey

            , mapMaybe
            , mapMaybeWithKey
            , mapEither
            , mapEitherWithKey

            , split
            , splitLookup

            -- * Submap
            , isSubmapOf, isSubmapOfBy
            , isProperSubmapOf, isProperSubmapOfBy

            -- * Min\/Max
            , findMin
            , findMax
            , deleteMin
            , deleteMax
            , deleteFindMin
            , deleteFindMax
            , updateMin
            , updateMax
            , updateMinWithKey
            , updateMaxWithKey
            , minView
            , maxView
            , minViewWithKey
            , maxViewWithKey

            -- * Debugging
            , showTree
            , showTreeWith
            ) where

import Prelude hiding (lookup,map,filter,foldr,foldl,null)

import Data.Bits
import Data.IntMap.Base hiding
    ( findWithDefault
    , singleton
    , insert
    , insertWith
    , insertWithKey
    , insertLookupWithKey
    , adjust
    , adjustWithKey
    , update
    , updateWithKey
    , updateLookupWithKey
    , alter
    , unionsWith
    , unionWith
    , unionWithKey
    , differenceWith
    , differenceWithKey
    , intersectionWith
    , intersectionWithKey
    , mergeWithKey
    , updateMinWithKey
    , updateMaxWithKey
    , updateMax
    , updateMin
    , map
    , mapWithKey
    , mapAccum
    , mapAccumWithKey
    , mapAccumRWithKey
    , mapKeysWith
    , mapMaybe
    , mapMaybeWithKey
    , mapEither
    , mapEitherWithKey
    , fromSet
    , fromList
    , fromListWith
    , fromListWithKey
    , fromAscList
    , fromAscListWith
    , fromAscListWithKey
    , fromDistinctAscList
    )
import qualified Data.IntSet.Base as IntSet
import Data.StrictPair

-- $strictness
--
-- This module satisfies the following strictness properties:
--
-- 1. Key and value arguments are evaluated to WHNF;
--
-- 2. Keys and values are evaluated to WHNF before they are stored in
--    the map.
--
-- Here are some examples that illustrate the first property:
--
-- > insertWith (\ new old -> old) k undefined m  ==  undefined
-- > delete undefined m  ==  undefined
--
-- Here are some examples that illustrate the second property:
--
-- > map (\ v -> undefined) m  ==  undefined      -- m is not empty
-- > mapKeys (\ k -> undefined) m  ==  undefined  -- m is not empty

{--------------------------------------------------------------------
  Query
--------------------------------------------------------------------}

-- | /O(min(n,W))/. The expression @('findWithDefault' def k map)@
-- returns the value at key @k@ or returns @def@ when the key is not an
-- element of the map.
--
-- > findWithDefault 'x' 1 (fromList [(5,'a'), (3,'b')]) == 'x'
-- > findWithDefault 'x' 5 (fromList [(5,'a'), (3,'b')]) == 'a'

-- See IntMap.Base.Note: Local 'go' functions and capturing]
findWithDefault :: a -> Key -> IntMap a -> a
findWithDefault def k = def `seq` k `seq` go
  where
    go (Bin p m l r) | nomatch k p m = def
                     | zero k m  = go l
                     | otherwise = go r
    go (Tip kx x) | k == kx   = x
                  | otherwise = def
    go Nil = def

{--------------------------------------------------------------------
  Construction
--------------------------------------------------------------------}
-- | /O(1)/. A map of one element.
--
-- > singleton 1 'a'        == fromList [(1, 'a')]
-- > size (singleton 1 'a') == 1

singleton :: Key -> a -> IntMap a
singleton k x
  = x `seq` Tip k x
{-# INLINE singleton #-}

{--------------------------------------------------------------------
  Insert
--------------------------------------------------------------------}
-- | /O(min(n,W))/. Insert a new key\/value pair in the map.
-- If the key is already present in the map, the associated value is
-- replaced with the supplied value, i.e. 'insert' is equivalent to
-- @'insertWith' 'const'@.
--
-- > insert 5 'x' (fromList [(5,'a'), (3,'b')]) == fromList [(3, 'b'), (5, 'x')]
-- > insert 7 'x' (fromList [(5,'a'), (3,'b')]) == fromList [(3, 'b'), (5, 'a'), (7, 'x')]
-- > insert 5 'x' empty                         == singleton 5 'x'

insert :: Key -> a -> IntMap a -> IntMap a
insert k x t = k `seq` x `seq`
  case t of
    Bin p m l r
      | nomatch k p m -> join k (Tip k x) p t
      | zero k m      -> Bin p m (insert k x l) r
      | otherwise     -> Bin p m l (insert k x r)
    Tip ky _
      | k==ky         -> Tip k x
      | otherwise     -> join k (Tip k x) ky t
    Nil -> Tip k x

-- right-biased insertion, used by 'union'
-- | /O(min(n,W))/. Insert with a combining function.
-- @'insertWith' f key value mp@
-- will insert the pair (key, value) into @mp@ if key does
-- not exist in the map. If the key does exist, the function will
-- insert @f new_value old_value@.
--
-- > insertWith (++) 5 "xxx" (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "xxxa")]
-- > insertWith (++) 7 "xxx" (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "a"), (7, "xxx")]
-- > insertWith (++) 5 "xxx" empty                         == singleton 5 "xxx"

insertWith :: (a -> a -> a) -> Key -> a -> IntMap a -> IntMap a
insertWith f k x t
  = insertWithKey (\_ x' y' -> f x' y') k x t

-- | /O(min(n,W))/. Insert with a combining function.
-- @'insertWithKey' f key value mp@
-- will insert the pair (key, value) into @mp@ if key does
-- not exist in the map. If the key does exist, the function will
-- insert @f key new_value old_value@.
--
-- > let f key new_value old_value = (show key) ++ ":" ++ new_value ++ "|" ++ old_value
-- > insertWithKey f 5 "xxx" (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "5:xxx|a")]
-- > insertWithKey f 7 "xxx" (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "a"), (7, "xxx")]
-- > insertWithKey f 5 "xxx" empty                         == singleton 5 "xxx"
--
-- If the key exists in the map, this function is lazy in @x@ but strict
-- in the result of @f@.

insertWithKey :: (Key -> a -> a -> a) -> Key -> a -> IntMap a -> IntMap a
insertWithKey f k x t = k `seq` x `seq`
  case t of
    Bin p m l r
      | nomatch k p m -> join k (Tip k x) p t
      | zero k m      -> Bin p m (insertWithKey f k x l) r
      | otherwise     -> Bin p m l (insertWithKey f k x r)
    Tip ky y
      | k==ky         -> Tip k $! f k x y
      | otherwise     -> join k (Tip k x) ky t
    Nil -> Tip k x

-- | /O(min(n,W))/. The expression (@'insertLookupWithKey' f k x map@)
-- is a pair where the first element is equal to (@'lookup' k map@)
-- and the second element equal to (@'insertWithKey' f k x map@).
--
-- > let f key new_value old_value = (show key) ++ ":" ++ new_value ++ "|" ++ old_value
-- > insertLookupWithKey f 5 "xxx" (fromList [(5,"a"), (3,"b")]) == (Just "a", fromList [(3, "b"), (5, "5:xxx|a")])
-- > insertLookupWithKey f 7 "xxx" (fromList [(5,"a"), (3,"b")]) == (Nothing,  fromList [(3, "b"), (5, "a"), (7, "xxx")])
-- > insertLookupWithKey f 5 "xxx" empty                         == (Nothing,  singleton 5 "xxx")
--
-- This is how to define @insertLookup@ using @insertLookupWithKey@:
--
-- > let insertLookup kx x t = insertLookupWithKey (\_ a _ -> a) kx x t
-- > insertLookup 5 "x" (fromList [(5,"a"), (3,"b")]) == (Just "a", fromList [(3, "b"), (5, "x")])
-- > insertLookup 7 "x" (fromList [(5,"a"), (3,"b")]) == (Nothing,  fromList [(3, "b"), (5, "a"), (7, "x")])

insertLookupWithKey :: (Key -> a -> a -> a) -> Key -> a -> IntMap a -> (Maybe a, IntMap a)
insertLookupWithKey f k x t = k `seq` x `seq`
  case t of
    Bin p m l r
      | nomatch k p m -> Nothing `strictPair` join k (Tip k x) p t
      | zero k m      -> let (found,l') = insertLookupWithKey f k x l in (found `strictPair` Bin p m l' r)
      | otherwise     -> let (found,r') = insertLookupWithKey f k x r in (found `strictPair` Bin p m l r')
    Tip ky y
      | k==ky         -> (Just y `strictPair` (Tip k $! f k x y))
      | otherwise     -> (Nothing `strictPair` join k (Tip k x) ky t)
    Nil -> Nothing `strictPair` Tip k x


{--------------------------------------------------------------------
  Deletion
--------------------------------------------------------------------}
-- | /O(min(n,W))/. Adjust a value at a specific key. When the key is not
-- a member of the map, the original map is returned.
--
-- > adjust ("new " ++) 5 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "new a")]
-- > adjust ("new " ++) 7 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "a")]
-- > adjust ("new " ++) 7 empty                         == empty

adjust ::  (a -> a) -> Key -> IntMap a -> IntMap a
adjust f k m
  = adjustWithKey (\_ x -> f x) k m

-- | /O(min(n,W))/. Adjust a value at a specific key. When the key is not
-- a member of the map, the original map is returned.
--
-- > let f key x = (show key) ++ ":new " ++ x
-- > adjustWithKey f 5 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "5:new a")]
-- > adjustWithKey f 7 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "a")]
-- > adjustWithKey f 7 empty                         == empty

adjustWithKey ::  (Key -> a -> a) -> Key -> IntMap a -> IntMap a
adjustWithKey f
  = updateWithKey (\k' x -> Just (f k' x))

-- | /O(min(n,W))/. The expression (@'update' f k map@) updates the value @x@
-- at @k@ (if it is in the map). If (@f x@) is 'Nothing', the element is
-- deleted. If it is (@'Just' y@), the key @k@ is bound to the new value @y@.
--
-- > let f x = if x == "a" then Just "new a" else Nothing
-- > update f 5 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "new a")]
-- > update f 7 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "a")]
-- > update f 3 (fromList [(5,"a"), (3,"b")]) == singleton 5 "a"

update ::  (a -> Maybe a) -> Key -> IntMap a -> IntMap a
update f
  = updateWithKey (\_ x -> f x)

-- | /O(min(n,W))/. The expression (@'update' f k map@) updates the value @x@
-- at @k@ (if it is in the map). If (@f k x@) is 'Nothing', the element is
-- deleted. If it is (@'Just' y@), the key @k@ is bound to the new value @y@.
--
-- > let f k x = if x == "a" then Just ((show k) ++ ":new a") else Nothing
-- > updateWithKey f 5 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "5:new a")]
-- > updateWithKey f 7 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "a")]
-- > updateWithKey f 3 (fromList [(5,"a"), (3,"b")]) == singleton 5 "a"

updateWithKey ::  (Key -> a -> Maybe a) -> Key -> IntMap a -> IntMap a
updateWithKey f k t = k `seq`
  case t of
    Bin p m l r
      | nomatch k p m -> t
      | zero k m      -> bin p m (updateWithKey f k l) r
      | otherwise     -> bin p m l (updateWithKey f k r)
    Tip ky y
      | k==ky         -> case f k y of
                           Just y' -> y' `seq` Tip ky y'
                           Nothing -> Nil
      | otherwise     -> t
    Nil -> Nil

-- | /O(min(n,W))/. Lookup and update.
-- The function returns original value, if it is updated.
-- This is different behavior than 'Data.Map.updateLookupWithKey'.
-- Returns the original key value if the map entry is deleted.
--
-- > let f k x = if x == "a" then Just ((show k) ++ ":new a") else Nothing
-- > updateLookupWithKey f 5 (fromList [(5,"a"), (3,"b")]) == (Just "a", fromList [(3, "b"), (5, "5:new a")])
-- > updateLookupWithKey f 7 (fromList [(5,"a"), (3,"b")]) == (Nothing,  fromList [(3, "b"), (5, "a")])
-- > updateLookupWithKey f 3 (fromList [(5,"a"), (3,"b")]) == (Just "b", singleton 5 "a")

updateLookupWithKey ::  (Key -> a -> Maybe a) -> Key -> IntMap a -> (Maybe a,IntMap a)
updateLookupWithKey f k t = k `seq`
  case t of
    Bin p m l r
      | nomatch k p m -> (Nothing, t)
      | zero k m      -> let (found,l') = updateLookupWithKey f k l in (found `strictPair` bin p m l' r)
      | otherwise     -> let (found,r') = updateLookupWithKey f k r in (found `strictPair` bin p m l r')
    Tip ky y
      | k==ky         -> case f k y of
                           Just y' -> y' `seq` (Just y `strictPair` Tip ky y')
                           Nothing -> (Just y, Nil)
      | otherwise     -> (Nothing,t)
    Nil -> (Nothing,Nil)



-- | /O(log n)/. The expression (@'alter' f k map@) alters the value @x@ at @k@, or absence thereof.
-- 'alter' can be used to insert, delete, or update a value in an 'IntMap'.
-- In short : @'lookup' k ('alter' f k m) = f ('lookup' k m)@.
alter :: (Maybe a -> Maybe a) -> Key -> IntMap a -> IntMap a
alter f k t = k `seq`
  case t of
    Bin p m l r
      | nomatch k p m -> case f Nothing of
                           Nothing -> t
                           Just x  -> x `seq` join k (Tip k x) p t
      | zero k m      -> bin p m (alter f k l) r
      | otherwise     -> bin p m l (alter f k r)
    Tip ky y
      | k==ky         -> case f (Just y) of
                           Just  x -> x `seq` Tip ky x
                           Nothing -> Nil
      | otherwise     -> case f Nothing of
                           Just x  -> x `seq` join k (Tip k x) ky t
                           Nothing -> t
    Nil               -> case f Nothing of
                           Just x  -> x `seq` Tip k x
                           Nothing -> Nil


{--------------------------------------------------------------------
  Union
--------------------------------------------------------------------}
-- | The union of a list of maps, with a combining operation.
--
-- > unionsWith (++) [(fromList [(5, "a"), (3, "b")]), (fromList [(5, "A"), (7, "C")]), (fromList [(5, "A3"), (3, "B3")])]
-- >     == fromList [(3, "bB3"), (5, "aAA3"), (7, "C")]

unionsWith :: (a->a->a) -> [IntMap a] -> IntMap a
unionsWith f ts
  = foldlStrict (unionWith f) empty ts

-- | /O(n+m)/. The union with a combining function.
--
-- > unionWith (++) (fromList [(5, "a"), (3, "b")]) (fromList [(5, "A"), (7, "C")]) == fromList [(3, "b"), (5, "aA"), (7, "C")]

unionWith :: (a -> a -> a) -> IntMap a -> IntMap a -> IntMap a
unionWith f m1 m2
  = unionWithKey (\_ x y -> f x y) m1 m2

-- | /O(n+m)/. The union with a combining function.
--
-- > let f key left_value right_value = (show key) ++ ":" ++ left_value ++ "|" ++ right_value
-- > unionWithKey f (fromList [(5, "a"), (3, "b")]) (fromList [(5, "A"), (7, "C")]) == fromList [(3, "b"), (5, "5:a|A"), (7, "C")]

unionWithKey :: (Key -> a -> a -> a) -> IntMap a -> IntMap a -> IntMap a
unionWithKey f m1 m2
  = mergeWithKey' Bin (\(Tip k1 x1) (Tip _k2 x2) -> Tip k1 $! f k1 x1 x2) id id m1 m2

{--------------------------------------------------------------------
  Difference
--------------------------------------------------------------------}

-- | /O(n+m)/. Difference with a combining function.
--
-- > let f al ar = if al == "b" then Just (al ++ ":" ++ ar) else Nothing
-- > differenceWith f (fromList [(5, "a"), (3, "b")]) (fromList [(5, "A"), (3, "B"), (7, "C")])
-- >     == singleton 3 "b:B"

differenceWith :: (a -> b -> Maybe a) -> IntMap a -> IntMap b -> IntMap a
differenceWith f m1 m2
  = differenceWithKey (\_ x y -> f x y) m1 m2

-- | /O(n+m)/. Difference with a combining function. When two equal keys are
-- encountered, the combining function is applied to the key and both values.
-- If it returns 'Nothing', the element is discarded (proper set difference).
-- If it returns (@'Just' y@), the element is updated with a new value @y@.
--
-- > let f k al ar = if al == "b" then Just ((show k) ++ ":" ++ al ++ "|" ++ ar) else Nothing
-- > differenceWithKey f (fromList [(5, "a"), (3, "b")]) (fromList [(5, "A"), (3, "B"), (10, "C")])
-- >     == singleton 3 "3:b|B"

differenceWithKey :: (Key -> a -> b -> Maybe a) -> IntMap a -> IntMap b -> IntMap a
differenceWithKey f m1 m2
  = mergeWithKey f id (const Nil) m1 m2

{--------------------------------------------------------------------
  Intersection
--------------------------------------------------------------------}

-- | /O(n+m)/. The intersection with a combining function.
--
-- > intersectionWith (++) (fromList [(5, "a"), (3, "b")]) (fromList [(5, "A"), (7, "C")]) == singleton 5 "aA"

intersectionWith :: (a -> b -> c) -> IntMap a -> IntMap b -> IntMap c
intersectionWith f m1 m2
  = intersectionWithKey (\_ x y -> f x y) m1 m2

-- | /O(n+m)/. The intersection with a combining function.
--
-- > let f k al ar = (show k) ++ ":" ++ al ++ "|" ++ ar
-- > intersectionWithKey f (fromList [(5, "a"), (3, "b")]) (fromList [(5, "A"), (7, "C")]) == singleton 5 "5:a|A"

intersectionWithKey :: (Key -> a -> b -> c) -> IntMap a -> IntMap b -> IntMap c
intersectionWithKey f m1 m2
  = mergeWithKey' bin (\(Tip k1 x1) (Tip _k2 x2) -> Tip k1 $! f k1 x1 x2) (const Nil) (const Nil) m1 m2

{--------------------------------------------------------------------
  MergeWithKey
--------------------------------------------------------------------}

-- | /O(n+m)/. A high-performance universal combining function. Using
-- 'mergeWithKey', all combining functions can be defined without any loss of
-- efficiency (with exception of 'union', 'difference' and 'intersection',
-- where sharing of some nodes is lost with 'mergeWithKey').
--
-- Please make sure you know what is going on when using 'mergeWithKey',
-- otherwise you can be surprised by unexpected code growth or even
-- corruption of the data structure.
--
-- When 'mergeWithKey' is given three arguments, it is inlined to the call
-- site. You should therefore use 'mergeWithKey' only to define your custom
-- combining functions. For example, you could define 'unionWithKey',
-- 'differenceWithKey' and 'intersectionWithKey' as
--
-- > myUnionWithKey f m1 m2 = mergeWithKey (\k x1 x2 -> Just (f k x1 x2)) id id m1 m2
-- > myDifferenceWithKey f m1 m2 = mergeWithKey f id (const empty) m1 m2
-- > myIntersectionWithKey f m1 m2 = mergeWithKey (\k x1 x2 -> Just (f k x1 x2)) (const empty) (const empty) m1 m2
--
-- When calling @'mergeWithKey' combine only1 only2@, a function combining two
-- 'IntMap's is created, such that
--
-- * if a key is present in both maps, it is passed with both corresponding
--   values to the @combine@ function. Depending on the result, the key is either
--   present in the result with specified value, or is left out;
--
-- * a nonempty subtree present only in the first map is passed to @only1@ and
--   the output is added to the result;
--
-- * a nonempty subtree present only in the second map is passed to @only2@ and
--   the output is added to the result.
--
-- The @only1@ and @only2@ methods /must return a map with a subset (possibly empty) of the keys of the given map/.
-- The values can be modified arbitrarily.  Most common variants of @only1@ and
-- @only2@ are 'id' and @'const' 'empty'@, but for example @'map' f@ or
-- @'filterWithKey' f@ could be used for any @f@.

mergeWithKey :: (Key -> a -> b -> Maybe c) -> (IntMap a -> IntMap c) -> (IntMap b -> IntMap c)
             -> IntMap a -> IntMap b -> IntMap c
mergeWithKey f g1 g2 = mergeWithKey' bin combine g1 g2
  where -- We use the lambda form to avoid non-exhaustive pattern matches warning.
        combine = \(Tip k1 x1) (Tip _k2 x2) -> case f k1 x1 x2 of Nothing -> Nil
                                                                  Just x -> x `seq` Tip k1 x
        {-# INLINE combine #-}
{-# INLINE mergeWithKey #-}

{--------------------------------------------------------------------
  Min\/Max
--------------------------------------------------------------------}

-- | /O(log n)/. Update the value at the minimal key.
--
-- > updateMinWithKey (\ k a -> Just ((show k) ++ ":" ++ a)) (fromList [(5,"a"), (3,"b")]) == fromList [(3,"3:b"), (5,"a")]
-- > updateMinWithKey (\ _ _ -> Nothing)                     (fromList [(5,"a"), (3,"b")]) == singleton 5 "a"

updateMinWithKey :: (Key -> a -> Maybe a) -> IntMap a -> IntMap a
updateMinWithKey f t =
  case t of Bin p m l r | m < 0 -> bin p m l (go f r)
            _ -> go f t
  where
    go f' (Bin p m l r) = bin p m (go f' l) r
    go f' (Tip k y) = case f' k y of
                        Just y' -> y' `seq` Tip k y'
                        Nothing -> Nil
    go _ Nil = error "updateMinWithKey Nil"

-- | /O(log n)/. Update the value at the maximal key.
--
-- > updateMaxWithKey (\ k a -> Just ((show k) ++ ":" ++ a)) (fromList [(5,"a"), (3,"b")]) == fromList [(3,"b"), (5,"5:a")]
-- > updateMaxWithKey (\ _ _ -> Nothing)                     (fromList [(5,"a"), (3,"b")]) == singleton 3 "b"

updateMaxWithKey :: (Key -> a -> Maybe a) -> IntMap a -> IntMap a
updateMaxWithKey f t =
  case t of Bin p m l r | m < 0 -> bin p m (go f l) r
            _ -> go f t
  where
    go f' (Bin p m l r) = bin p m l (go f' r)
    go f' (Tip k y) = case f' k y of
                        Just y' -> y' `seq` Tip k y'
                        Nothing -> Nil
    go _ Nil = error "updateMaxWithKey Nil"

-- | /O(log n)/. Update the value at the maximal key.
--
-- > updateMax (\ a -> Just ("X" ++ a)) (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "Xa")]
-- > updateMax (\ _ -> Nothing)         (fromList [(5,"a"), (3,"b")]) == singleton 3 "b"

updateMax :: (a -> Maybe a) -> IntMap a -> IntMap a
updateMax f = updateMaxWithKey (const f)

-- | /O(log n)/. Update the value at the minimal key.
--
-- > updateMin (\ a -> Just ("X" ++ a)) (fromList [(5,"a"), (3,"b")]) == fromList [(3, "Xb"), (5, "a")]
-- > updateMin (\ _ -> Nothing)         (fromList [(5,"a"), (3,"b")]) == singleton 5 "a"

updateMin :: (a -> Maybe a) -> IntMap a -> IntMap a
updateMin f = updateMinWithKey (const f)


{--------------------------------------------------------------------
  Mapping
--------------------------------------------------------------------}
-- | /O(n)/. Map a function over all values in the map.
--
-- > map (++ "x") (fromList [(5,"a"), (3,"b")]) == fromList [(3, "bx"), (5, "ax")]

map :: (a -> b) -> IntMap a -> IntMap b
map f t
  = case t of
      Bin p m l r -> Bin p m (map f l) (map f r)
      Tip k x     -> Tip k $! f x
      Nil         -> Nil

-- | /O(n)/. Map a function over all values in the map.
--
-- > let f key x = (show key) ++ ":" ++ x
-- > mapWithKey f (fromList [(5,"a"), (3,"b")]) == fromList [(3, "3:b"), (5, "5:a")]

mapWithKey :: (Key -> a -> b) -> IntMap a -> IntMap b
mapWithKey f t
  = case t of
      Bin p m l r -> Bin p m (mapWithKey f l) (mapWithKey f r)
      Tip k x     -> Tip k $! f k x
      Nil         -> Nil

-- | /O(n)/. The function @'mapAccum'@ threads an accumulating
-- argument through the map in ascending order of keys.
--
-- > let f a b = (a ++ b, b ++ "X")
-- > mapAccum f "Everything: " (fromList [(5,"a"), (3,"b")]) == ("Everything: ba", fromList [(3, "bX"), (5, "aX")])

mapAccum :: (a -> b -> (a,c)) -> a -> IntMap b -> (a,IntMap c)
mapAccum f = mapAccumWithKey (\a' _ x -> f a' x)

-- | /O(n)/. The function @'mapAccumWithKey'@ threads an accumulating
-- argument through the map in ascending order of keys.
--
-- > let f a k b = (a ++ " " ++ (show k) ++ "-" ++ b, b ++ "X")
-- > mapAccumWithKey f "Everything:" (fromList [(5,"a"), (3,"b")]) == ("Everything: 3-b 5-a", fromList [(3, "bX"), (5, "aX")])

mapAccumWithKey :: (a -> Key -> b -> (a,c)) -> a -> IntMap b -> (a,IntMap c)
mapAccumWithKey f a t
  = mapAccumL f a t

-- | /O(n)/. The function @'mapAccumL'@ threads an accumulating
-- argument through the map in ascending order of keys.  Strict in
-- the accumulating argument and the both elements of the
-- result of the function.
mapAccumL :: (a -> Key -> b -> (a,c)) -> a -> IntMap b -> (a,IntMap c)
mapAccumL f a t
  = case t of
      Bin p m l r -> let (a1,l') = mapAccumL f a l
                         (a2,r') = mapAccumL f a1 r
                     in (a2 `strictPair` Bin p m l' r')
      Tip k x     -> let (a',x') = f a k x in x' `seq` (a' `strictPair` Tip k x')
      Nil         -> (a `strictPair` Nil)

-- | /O(n)/. The function @'mapAccumR'@ threads an accumulating
-- argument through the map in descending order of keys.
mapAccumRWithKey :: (a -> Key -> b -> (a,c)) -> a -> IntMap b -> (a,IntMap c)
mapAccumRWithKey f a t
  = case t of
      Bin p m l r -> let (a1,r') = mapAccumRWithKey f a r
                         (a2,l') = mapAccumRWithKey f a1 l
                     in (a2 `strictPair` Bin p m l' r')
      Tip k x     -> let (a',x') = f a k x in x' `seq` (a' `strictPair` Tip k x')
      Nil         -> (a `strictPair` Nil)

-- | /O(n*log n)/.
-- @'mapKeysWith' c f s@ is the map obtained by applying @f@ to each key of @s@.
--
-- The size of the result may be smaller if @f@ maps two or more distinct
-- keys to the same new key.  In this case the associated values will be
-- combined using @c@.
--
-- > mapKeysWith (++) (\ _ -> 1) (fromList [(1,"b"), (2,"a"), (3,"d"), (4,"c")]) == singleton 1 "cdab"
-- > mapKeysWith (++) (\ _ -> 3) (fromList [(1,"b"), (2,"a"), (3,"d"), (4,"c")]) == singleton 3 "cdab"

mapKeysWith :: (a -> a -> a) -> (Key->Key) -> IntMap a -> IntMap a
mapKeysWith c f = fromListWith c . foldrWithKey (\k x xs -> (f k, x) : xs) []

{--------------------------------------------------------------------
  Filter
--------------------------------------------------------------------}
-- | /O(n)/. Map values and collect the 'Just' results.
--
-- > let f x = if x == "a" then Just "new a" else Nothing
-- > mapMaybe f (fromList [(5,"a"), (3,"b")]) == singleton 5 "new a"

mapMaybe :: (a -> Maybe b) -> IntMap a -> IntMap b
mapMaybe f = mapMaybeWithKey (\_ x -> f x)

-- | /O(n)/. Map keys\/values and collect the 'Just' results.
--
-- > let f k _ = if k < 5 then Just ("key : " ++ (show k)) else Nothing
-- > mapMaybeWithKey f (fromList [(5,"a"), (3,"b")]) == singleton 3 "key : 3"

mapMaybeWithKey :: (Key -> a -> Maybe b) -> IntMap a -> IntMap b
mapMaybeWithKey f (Bin p m l r)
  = bin p m (mapMaybeWithKey f l) (mapMaybeWithKey f r)
mapMaybeWithKey f (Tip k x) = case f k x of
  Just y  -> y `seq` Tip k y
  Nothing -> Nil
mapMaybeWithKey _ Nil = Nil

-- | /O(n)/. Map values and separate the 'Left' and 'Right' results.
--
-- > let f a = if a < "c" then Left a else Right a
-- > mapEither f (fromList [(5,"a"), (3,"b"), (1,"x"), (7,"z")])
-- >     == (fromList [(3,"b"), (5,"a")], fromList [(1,"x"), (7,"z")])
-- >
-- > mapEither (\ a -> Right a) (fromList [(5,"a"), (3,"b"), (1,"x"), (7,"z")])
-- >     == (empty, fromList [(5,"a"), (3,"b"), (1,"x"), (7,"z")])

mapEither :: (a -> Either b c) -> IntMap a -> (IntMap b, IntMap c)
mapEither f m
  = mapEitherWithKey (\_ x -> f x) m

-- | /O(n)/. Map keys\/values and separate the 'Left' and 'Right' results.
--
-- > let f k a = if k < 5 then Left (k * 2) else Right (a ++ a)
-- > mapEitherWithKey f (fromList [(5,"a"), (3,"b"), (1,"x"), (7,"z")])
-- >     == (fromList [(1,2), (3,6)], fromList [(5,"aa"), (7,"zz")])
-- >
-- > mapEitherWithKey (\_ a -> Right a) (fromList [(5,"a"), (3,"b"), (1,"x"), (7,"z")])
-- >     == (empty, fromList [(1,"x"), (3,"b"), (5,"a"), (7,"z")])

mapEitherWithKey :: (Key -> a -> Either b c) -> IntMap a -> (IntMap b, IntMap c)
mapEitherWithKey f (Bin p m l r)
  = bin p m l1 r1 `strictPair` bin p m l2 r2
  where
    (l1,l2) = mapEitherWithKey f l
    (r1,r2) = mapEitherWithKey f r
mapEitherWithKey f (Tip k x) = case f k x of
  Left y  -> y `seq` (Tip k y, Nil)
  Right z -> z `seq` (Nil, Tip k z)
mapEitherWithKey _ Nil = (Nil, Nil)

{--------------------------------------------------------------------
  Conversions
--------------------------------------------------------------------}

-- | /O(n)/. Build a map from a set of keys and a function which for each key
-- computes its value.
--
-- > fromSet (\k -> replicate k 'a') (Data.IntSet.fromList [3, 5]) == fromList [(5,"aaaaa"), (3,"aaa")]
-- > fromSet undefined Data.IntSet.empty == empty

fromSet :: (Key -> a) -> IntSet.IntSet -> IntMap a
fromSet _ IntSet.Nil = Nil
fromSet f (IntSet.Bin p m l r) = Bin p m (fromSet f l) (fromSet f r)
fromSet f (IntSet.Tip kx bm) = buildTree f kx bm (IntSet.suffixBitMask + 1)
  where -- This is slightly complicated, as we to convert the dense
        -- representation of IntSet into tree representation of IntMap.
        --
        -- We are given a nonzero bit mask 'bmask' of 'bits' bits with prefix 'prefix'.
        -- We split bmask into halves corresponding to left and right subtree.
        -- If they are both nonempty, we create a Bin node, otherwise exactly
        -- one of them is nonempty and we construct the IntMap from that half.
        buildTree g prefix bmask bits = prefix `seq` bmask `seq` case bits of
          0 -> Tip prefix $! g prefix
          _ -> case intFromNat ((natFromInt bits) `shiftRL` 1) of
                 bits2 | bmask .&. ((1 `shiftLL` bits2) - 1) == 0 ->
                           buildTree g (prefix + bits2) (bmask `shiftRL` bits2) bits2
                       | (bmask `shiftRL` bits2) .&. ((1 `shiftLL` bits2) - 1) == 0 ->
                           buildTree g prefix bmask bits2
                       | otherwise ->
                           Bin prefix bits2 (buildTree g prefix bmask bits2) (buildTree g (prefix + bits2) (bmask `shiftRL` bits2) bits2)

{--------------------------------------------------------------------
  Lists
--------------------------------------------------------------------}
-- | /O(n*min(n,W))/. Create a map from a list of key\/value pairs.
--
-- > fromList [] == empty
-- > fromList [(5,"a"), (3,"b"), (5, "c")] == fromList [(5,"c"), (3,"b")]
-- > fromList [(5,"c"), (3,"b"), (5, "a")] == fromList [(5,"a"), (3,"b")]

fromList :: [(Key,a)] -> IntMap a
fromList xs
  = foldlStrict ins empty xs
  where
    ins t (k,x)  = insert k x t

-- | /O(n*min(n,W))/. Create a map from a list of key\/value pairs with a combining function. See also 'fromAscListWith'.
--
-- > fromListWith (++) [(5,"a"), (5,"b"), (3,"b"), (3,"a"), (5,"a")] == fromList [(3, "ab"), (5, "aba")]
-- > fromListWith (++) [] == empty

fromListWith :: (a -> a -> a) -> [(Key,a)] -> IntMap a
fromListWith f xs
  = fromListWithKey (\_ x y -> f x y) xs

-- | /O(n*min(n,W))/. Build a map from a list of key\/value pairs with a combining function. See also fromAscListWithKey'.
--
-- > fromListWith (++) [(5,"a"), (5,"b"), (3,"b"), (3,"a"), (5,"a")] == fromList [(3, "ab"), (5, "aba")]
-- > fromListWith (++) [] == empty

fromListWithKey :: (Key -> a -> a -> a) -> [(Key,a)] -> IntMap a
fromListWithKey f xs
  = foldlStrict ins empty xs
  where
    ins t (k,x) = insertWithKey f k x t

-- | /O(n)/. Build a map from a list of key\/value pairs where
-- the keys are in ascending order.
--
-- > fromAscList [(3,"b"), (5,"a")]          == fromList [(3, "b"), (5, "a")]
-- > fromAscList [(3,"b"), (5,"a"), (5,"b")] == fromList [(3, "b"), (5, "b")]

fromAscList :: [(Key,a)] -> IntMap a
fromAscList xs
  = fromAscListWithKey (\_ x _ -> x) xs

-- | /O(n)/. Build a map from a list of key\/value pairs where
-- the keys are in ascending order, with a combining function on equal keys.
-- /The precondition (input list is ascending) is not checked./
--
-- > fromAscListWith (++) [(3,"b"), (5,"a"), (5,"b")] == fromList [(3, "b"), (5, "ba")]

fromAscListWith :: (a -> a -> a) -> [(Key,a)] -> IntMap a
fromAscListWith f xs
  = fromAscListWithKey (\_ x y -> f x y) xs

-- | /O(n)/. Build a map from a list of key\/value pairs where
-- the keys are in ascending order, with a combining function on equal keys.
-- /The precondition (input list is ascending) is not checked./
--
-- > fromAscListWith (++) [(3,"b"), (5,"a"), (5,"b")] == fromList [(3, "b"), (5, "ba")]

fromAscListWithKey :: (Key -> a -> a -> a) -> [(Key,a)] -> IntMap a
fromAscListWithKey _ []         = Nil
fromAscListWithKey f (x0 : xs0) = fromDistinctAscList (combineEq x0 xs0)
  where
    -- [combineEq f xs] combines equal elements with function [f] in an ordered list [xs]
    combineEq z [] = [z]
    combineEq z@(kz,zz) (x@(kx,xx):xs)
      | kx==kz    = let yy = f kx xx zz in yy `seq` combineEq (kx,yy) xs
      | otherwise = z:combineEq x xs

-- | /O(n)/. Build a map from a list of key\/value pairs where
-- the keys are in ascending order and all distinct.
-- /The precondition (input list is strictly ascending) is not checked./
--
-- > fromDistinctAscList [(3,"b"), (5,"a")] == fromList [(3, "b"), (5, "a")]

fromDistinctAscList :: [(Key,a)] -> IntMap a
fromDistinctAscList []         = Nil
fromDistinctAscList (z0 : zs0) = work z0 zs0 Nada
  where
    work (kx,vx) []            stk = vx `seq` finish kx (Tip kx vx) stk
    work (kx,vx) (z@(kz,_):zs) stk = vx `seq` reduce z zs (branchMask kx kz) kx (Tip kx vx) stk

    reduce :: (Key,a) -> [(Key,a)] -> Mask -> Prefix -> IntMap a -> Stack a -> IntMap a
    reduce z zs _ px tx Nada = work z zs (Push px tx Nada)
    reduce z zs m px tx stk@(Push py ty stk') =
        let mxy = branchMask px py
            pxy = mask px mxy
        in  if shorter m mxy
                 then reduce z zs m pxy (Bin pxy mxy ty tx) stk'
                 else work z zs (Push px tx stk)

    finish _  t  Nada = t
    finish px tx (Push py ty stk) = finish p (join py ty px tx) stk
        where m = branchMask px py
              p = mask px m

data Stack a = Push {-# UNPACK #-} !Prefix !(IntMap a) !(Stack a) | Nada
