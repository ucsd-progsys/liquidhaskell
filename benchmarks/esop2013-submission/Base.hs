{-@ LIQUID "--totality" @-}
{-@ LIQUID "--prune-unsorted" @-}
{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__
-- LIQUID {- LANGUAGE DeriveDataTypeable, StandaloneDeriving -}
#endif
#if !defined(TESTING) && __GLASGOW_HASKELL__ >= 703
{-# LANGUAGE Trustworthy #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Map.Base
-- Copyright   :  (c) Daan Leijen 2002
--                (c) Andriy Palamarchuk 2008
-- License     :  BSD-style
-- Maintainer  :  libraries@haskell.org
-- Stability   :  provisional
-- Portability :  portable
--
-- An efficient implementation of maps from keys to values (dictionaries).
--
-- Since many function names (but not the type name) clash with
-- "Prelude" names, this module is usually imported @qualified@, e.g.
--
-- >  import Data.Map (Map)
-- >  import qualified Data.Map as Map
--
-- The implementation of 'Map' is based on /size balanced/ binary trees (or
-- trees of /bounded balance/) as described by:
--
--    * Stephen Adams, \"/Efficient sets: a balancing act/\",
--     Journal of Functional Programming 3(4):553-562, October 1993,
--     <http://www.swiss.ai.mit.edu/~adams/BB/>.
--
--    * J. Nievergelt and E.M. Reingold,
--      \"/Binary search trees of bounded balance/\",
--      SIAM journal of computing 2(1), March 1973.
--
-- Note that the implementation is /left-biased/ -- the elements of a
-- first argument are always preferred to the second, for example in
-- 'union' or 'insert'.
--
-- Operation comments contain the operation time complexity in
-- the Big-O notation <http://en.wikipedia.org/wiki/Big_O_notation>.
-----------------------------------------------------------------------------

-- [Note: Using INLINABLE]
-- ~~~~~~~~~~~~~~~~~~~~~~~
-- It is crucial to the performance that the functions specialize on the Ord
-- type when possible. GHC 7.0 and higher does this by itself when it sees th
-- unfolding of a function -- that is why all public functions are marked
-- INLINABLE (that exposes the unfolding).


-- [Note: Using INLINE]
-- ~~~~~~~~~~~~~~~~~~~~
-- For other compilers and GHC pre 7.0, we mark some of the functions INLINE.
-- We mark the functions that just navigate down the tree (lookup, insert,
-- delete and similar). That navigation code gets inlined and thus specialized
-- when possible. There is a price to pay -- code growth. The code INLINED is
-- therefore only the tree navigation, all the real work (rebalancing) is not
-- INLINED by using a NOINLINE.
--
-- All methods marked INLINE have to be nonrecursive -- a 'go' function doing
-- the real work is provided.


-- [Note: Type of local 'go' function]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- If the local 'go' function uses an Ord class, it sometimes heap-allocates
-- the Ord dictionary when the 'go' function does not have explicit type.
-- In that case we give 'go' explicit type. But this slightly decrease
-- performance, as the resulting 'go' function can float out to top level.


-- [Note: Local 'go' functions and capturing]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- As opposed to IntMap, when 'go' function captures an argument, increased
-- heap-allocation can occur: sometimes in a polymorphic function, the 'go'
-- floats out of its enclosing function and then it heap-allocates the
-- dictionary and the argument. Maybe it floats out too late and strictness
-- analyzer cannot see that these could be passed on stack.
--
-- For example, change 'member' so that its local 'go' function is not passing
-- argument k and then look at the resulting code for hedgeInt.


-- [Note: Order of constructors]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- The order of constructors of Map matters when considering performance.
-- Currently in GHC 7.0, when type has 2 constructors, a forward conditional
-- jump is made when successfully matching second constructor. Successful match
-- of first constructor results in the forward jump not taken.
-- On GHC 7.0, reordering constructors from Tip | Bin to Bin | Tip
-- improves the benchmark by up to 10% on x86.

module Data.Map.Base (
            -- * Map type
              Map(..)          -- instance Eq,Show,Read

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
            -- LIQUID, traverseWithKey
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
            -- LIQUID, keysSet
            -- LIQUID, fromSet

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

            -- * Indexed
            , lookupIndex
            , findIndex
            , elemAt
            , updateAt
            , deleteAt

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
            , valid

            -- Used by the strict version
            , bin
            , balance
            , balanced
            , balanceL
            , balanceR
            , delta
            , join
            , merge
            , glue
            , trim, zoo1, zoo2
            , trimLookupLo
            , foldlStrict
            , MaybeS(..)
            , filterGt
            , filterLt
            ) where

import Prelude hiding (lookup,map,filter,foldr,foldl,null)
-- LIQUID import qualified Data.Set.Base as Set
-- LIQUID import Data.StrictPair
import Data.Monoid (Monoid(..))
-- LIQUID import Control.Applicative (Applicative(..), (<$>))
import Data.Traversable (Traversable(traverse))
import qualified Data.Foldable as Foldable
-- import Data.Typeable
import Control.DeepSeq (NFData(rnf))

#if __GLASGOW_HASKELL__
import GHC.Exts ( build )
import Text.Read
import Data.Data
#endif

-- Use macros to define strictness of functions.
-- STRICT_x_OF_y denotes an y-ary function strict in the x-th parameter.
-- We do not use BangPatterns, because they are not in any standard and we
-- want the compilers to be compiled by as many compilers as possible.
#define STRICT_1_OF_2(fn) fn arg _ | arg `seq` False = undefined
#define STRICT_1_OF_3(fn) fn arg _ _ | arg `seq` False = undefined
#define STRICT_2_OF_3(fn) fn _ arg _ | arg `seq` False = undefined
#define STRICT_1_OF_4(fn) fn arg _ _ _ | arg `seq` False = undefined
#define STRICT_2_OF_4(fn) fn _ arg _ _ | arg `seq` False = undefined

{--------------------------------------------------------------------
  Operators
--------------------------------------------------------------------}
infixl 9 !,\\ --

-- | /O(log n)/. Find the value at a key.
-- Calls 'error' when the element can not be found.
--
-- > fromList [(5,'a'), (3,'b')] ! 1    Error: element not in the map
-- > fromList [(5,'a'), (3,'b')] ! 5 == 'a'

{-@ Data.Map.Base.! :: (Ord k) => OMap k a -> k -> a @-}
(!) :: Ord k => Map k a -> k -> a
m ! k = find k m
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE (!) #-}
#endif

-- | Same as 'difference'.
{-@ Data.Map.Base.\\ :: Ord k => OMap k a -> OMap k b -> OMap k a @-}
(\\) :: Ord k => Map k a -> Map k b -> Map k a
m1 \\ m2 = difference m1 m2
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE (\\) #-}
#endif

{--------------------------------------------------------------------
  Size balanced trees.
--------------------------------------------------------------------}
-- | A Map from keys @k@ to values @a@.

-- See Note: Order of constructors
data Map k a  = Bin Size k a (Map k a) (Map k a)
              | Tip

type Size     = Int

{-@ include <Base.hquals> @-}

{-@ data Map [mlen] k a <l :: root:k -> k -> Prop, r :: root:k -> k -> Prop>
         = Bin (sz    :: Size) 
               (key   :: k) 
               (value :: a) 
               (left  :: Map <l, r> (k <l key>) a) 
               (right :: Map <l, r> (k <r key>) a) 
         | Tip 
  @-}

{-@ measure mlen :: (Map k a) -> Int
    mlen(Tip) = 0
    mlen(Bin s k v l r) = 1 + (mlen l) + (mlen r)
  @-}

{-@ type SumMLen A B = {v:Nat | v = (mlen A) + (mlen B)} @-}

{-@ invariant {v:Map k a | (mlen v) >= 0} @-}


{-@ mlen :: m:Map k a -> {v:Nat | v = (mlen m)} @-}
mlen :: Map k a -> Int
mlen Tip = 0
mlen (Bin s k v l r) = 1 + mlen l + mlen r

{-@ type OMap k a = Map <{\root v -> v < root}, {\root v -> v > root}> k a @-}

{-@ measure isJustS :: forall a. MaybeS a -> Prop
    isJustS (JustS x)  = true
    isJustS (NothingS) = false
@-}

{-@ measure fromJustS :: forall a. MaybeS a -> a 
    fromJustS (JustS x) = x 
  @-}

{-@ measure isBin :: Map k a -> Prop
    isBin (Bin sz kx x l r) = true
    isBin (Tip)             = false
  @-}

{-@ invariant {v0: MaybeS {v: a | ((isJustS v0) && (v = (fromJustS v0)))} | true} @-}

{-@ predicate IfDefLe X Y         = ((isJustS X) => ((fromJustS X) < Y)) @-}
{-@ predicate IfDefLt X Y         = ((isJustS X) => ((fromJustS X) < Y)) @-}
{-@ predicate IfDefGt X Y         = ((isJustS X) => (Y < (fromJustS X))) @-}
{-@ predicate RootLt Lo V         = ((isBin V) => (IfDefLt Lo (key V)))  @-}
{-@ predicate RootGt Hi V         = ((isBin V) => (IfDefGt Hi (key V)))  @-}
{-@ predicate RootBetween Lo Hi V = ((RootLt Lo V) && (RootGt Hi V))     @-}
{-@ predicate KeyBetween Lo Hi V  = ((IfDefLt Lo V) && (IfDefGt Hi V))   @-}


-- LIQUID instance (Ord k) => Monoid (Map k v) where
--     mempty  = empty
--     mappend = union
--     mconcat = unions

#if __GLASGOW_HASKELL__

{--------------------------------------------------------------------
  A Data instance
--------------------------------------------------------------------}

-- This instance preserves data abstraction at the cost of inefficiency.
-- We omit reflection services for the sake of data abstraction.
-- LIQUID instance (Data k, Data a, Ord k) => Data (Map k a) where
-- LIQUID   gfoldl f z m   = z fromList `f` toList m
-- LIQUID   toConstr _     = error "toConstr"
-- LIQUID   gunfold _ _    = error "gunfold"
-- LIQUID   dataTypeOf _   = mkNoRepType "Data.Map.Map"
-- LIQUID   dataCast2 f    = gcast2 f
#endif

{--------------------------------------------------------------------
  Query
--------------------------------------------------------------------}
-- | /O(1)/. Is the map empty?
--
-- > Data.Map.null (empty)           == True
-- > Data.Map.null (singleton 1 'a') == False

null :: Map k a -> Bool
null Tip      = True
null (Bin {}) = False
{-# INLINE null #-}

-- | /O(1)/. The number of elements in the map.
--
-- > size empty                                   == 0
-- > size (singleton 1 'a')                       == 1
-- > size (fromList([(1,'a'), (2,'c'), (3,'b')])) == 3

size :: Map k a -> Int
size Tip              = 0
size (Bin sz _ _ _ _) = sz
{-# INLINE size #-}


-- | /O(log n)/. Lookup the value at a key in the map.
--
-- The function will return the corresponding value as @('Just' value)@,
-- or 'Nothing' if the key isn't in the map.
--
-- An example of using @lookup@:
--
-- > import Prelude hiding (lookup)
-- > import Data.Map
-- >
-- > employeeDept = fromList([("John","Sales"), ("Bob","IT")])
-- > deptCountry = fromList([("IT","USA"), ("Sales","France")])
-- > countryCurrency = fromList([("USA", "Dollar"), ("France", "Euro")])
-- >
-- > employeeCurrency :: String -> Maybe String
-- > employeeCurrency name = do
-- >     dept <- lookup name employeeDept
-- >     country <- lookup dept deptCountry
-- >     lookup country countryCurrency
-- >
-- > main = do
-- >     putStrLn $ "John's currency: " ++ (show (employeeCurrency "John"))
-- >     putStrLn $ "Pete's currency: " ++ (show (employeeCurrency "Pete"))
--
-- The output of this program:
--
-- >   John's currency: Just "Euro"
-- >   Pete's currency: Nothing

{-@ lookup :: (Ord k) => k -> OMap k a -> Maybe a @-}
lookup :: Ord k => k -> Map k a -> Maybe a
lookup = go
  where
    STRICT_1_OF_2(go)
    go _ Tip = Nothing
    go k (Bin _ kx x l r) = case compare k kx of
      LT -> go k l
      GT -> go k r
      EQ -> Just x
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE lookup #-}
#else
{-# INLINE lookup #-}
#endif

-- | /O(log n)/. Is the key a member of the map? See also 'notMember'.
--
-- > member 5 (fromList [(5,'a'), (3,'b')]) == True
-- > member 1 (fromList [(5,'a'), (3,'b')]) == False

{-@ member :: (Ord k) => k -> OMap k a -> Bool @-}
member :: Ord k => k -> Map k a -> Bool
member = go
  where
    STRICT_1_OF_2(go)
    go _ Tip = False
    go k (Bin _ kx _ l r) = case compare k kx of
      LT -> go k l
      GT -> go k r
      EQ -> True
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE member #-}
#else
{-# INLINE member #-}
#endif

-- | /O(log n)/. Is the key not a member of the map? See also 'member'.
--
-- > notMember 5 (fromList [(5,'a'), (3,'b')]) == False
-- > notMember 1 (fromList [(5,'a'), (3,'b')]) == True

{-@ notMember :: (Ord k) => k -> OMap k a -> Bool @-}
notMember :: Ord k => k -> Map k a -> Bool
notMember k m = not $ member k m
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE notMember #-}
#else
{-# INLINE notMember #-}
#endif

-- | /O(log n)/. Find the value at a key.
-- Calls 'error' when the element can not be found.

{-@ find :: (Ord k) => k -> OMap k a -> a @-}
find :: Ord k => k -> Map k a -> a
find = go
  where
    STRICT_1_OF_2(go)
    go _ Tip = error "Map.!: given key is not an element in the map"
    go k (Bin _ kx x l r) = case compare k kx of
      LT -> go k l
      GT -> go k r
      EQ -> x
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE find #-}
#else
{-# INLINE find #-}
#endif

-- | /O(log n)/. The expression @('findWithDefault' def k map)@ returns
-- the value at key @k@ or returns default value @def@
-- when the key is not in the map.
--
-- > findWithDefault 'x' 1 (fromList [(5,'a'), (3,'b')]) == 'x'
-- > findWithDefault 'x' 5 (fromList [(5,'a'), (3,'b')]) == 'a'

{-@ findWithDefault :: (Ord k) => a -> k -> OMap k a -> a @-}
findWithDefault :: Ord k => a -> k -> Map k a -> a
findWithDefault = go
  where
    STRICT_2_OF_3(go)
    go def _ Tip = def
    go def k (Bin _ kx x l r) = case compare k kx of
      LT -> go def k l
      GT -> go def k r
      EQ -> x
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE findWithDefault #-}
#else
{-# INLINE findWithDefault #-}
#endif

-- | /O(log n)/. Find largest key smaller than the given one and return the
-- corresponding (key, value) pair.
--
-- > lookupLT 3 (fromList [(3,'a'), (5,'b')]) == Nothing
-- > lookupLT 4 (fromList [(3,'a'), (5,'b')]) == Just (3, 'a')
{-@ lookupLT :: (Ord k) => k -> OMap k v -> Maybe (k, v) @-}
lookupLT :: Ord k => k -> Map k v -> Maybe (k, v)
lookupLT = goNothing
  where
    STRICT_1_OF_2(goNothing)
    goNothing _ Tip = Nothing
    goNothing k (Bin _ kx x l r) | k <= kx = goNothing k l
                                 | otherwise = goJust k kx x r

    STRICT_1_OF_4(goJust)
    goJust _ kx' x' Tip = Just (kx', x')
    goJust k kx' x' (Bin _ kx x l r) | k <= kx = goJust k kx' x' l
                                     | otherwise = goJust k kx x r
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE lookupLT #-}
#else
{-# INLINE lookupLT #-}
#endif

-- | /O(log n)/. Find smallest key greater than the given one and return the
-- corresponding (key, value) pair.
--
-- > lookupGT 4 (fromList [(3,'a'), (5,'b')]) == Just (5, 'b')
-- > lookupGT 5 (fromList [(3,'a'), (5,'b')]) == Nothing
{-@ lookupGT :: (Ord k) => k -> OMap k v -> Maybe (k, v) @-}
lookupGT :: Ord k => k -> Map k v -> Maybe (k, v)
lookupGT = goNothing
  where
    STRICT_1_OF_2(goNothing)
    goNothing _ Tip = Nothing
    goNothing k (Bin _ kx x l r) | k < kx = goJust k kx x l
                                 | otherwise = goNothing k r

    STRICT_1_OF_4(goJust)
    goJust _ kx' x' Tip = Just (kx', x')
    goJust k kx' x' (Bin _ kx x l r) | k < kx = goJust k kx x l
                                     | otherwise = goJust k kx' x' r
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE lookupGT #-}
#else
{-# INLINE lookupGT #-}
#endif

-- | /O(log n)/. Find largest key smaller or equal to the given one and return
-- the corresponding (key, value) pair.
--
-- > lookupLE 2 (fromList [(3,'a'), (5,'b')]) == Nothing
-- > lookupLE 4 (fromList [(3,'a'), (5,'b')]) == Just (3, 'a')
-- > lookupLE 5 (fromList [(3,'a'), (5,'b')]) == Just (5, 'b')
{-@ lookupLE :: (Ord k) => k -> OMap k v -> Maybe (k, v) @-}
lookupLE :: Ord k => k -> Map k v -> Maybe (k, v)
lookupLE = goNothing
  where
    STRICT_1_OF_2(goNothing)
    goNothing _ Tip = Nothing
    goNothing k (Bin _ kx x l r) = case compare k kx of LT -> goNothing k l
                                                        EQ -> Just (kx, x)
                                                        GT -> goJust k kx x r

    STRICT_1_OF_4(goJust)
    goJust _ kx' x' Tip = Just (kx', x')
    goJust k kx' x' (Bin _ kx x l r) = case compare k kx of LT -> goJust k kx' x' l
                                                            EQ -> Just (kx, x)
                                                            GT -> goJust k kx x r
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE lookupLE #-}
#else
{-# INLINE lookupLE #-}
#endif

-- | /O(log n)/. Find smallest key greater or equal to the given one and return
-- the corresponding (key, value) pair.
--
-- > lookupGE 3 (fromList [(3,'a'), (5,'b')]) == Just (3, 'a')
-- > lookupGE 4 (fromList [(3,'a'), (5,'b')]) == Just (5, 'b')
-- > lookupGE 6 (fromList [(3,'a'), (5,'b')]) == Nothing
{-@ lookupGE :: (Ord k) => k -> OMap k v -> Maybe (k, v) @-}
lookupGE :: Ord k => k -> Map k v -> Maybe (k, v)
lookupGE = goNothing
  where
    STRICT_1_OF_2(goNothing)
    goNothing _ Tip = Nothing
    goNothing k (Bin _ kx x l r) = case compare k kx of LT -> goJust k kx x l
                                                        EQ -> Just (kx, x)
                                                        GT -> goNothing k r

    STRICT_1_OF_4(goJust)
    goJust _ kx' x' Tip = Just (kx', x')
    goJust k kx' x' (Bin _ kx x l r) = case compare k kx of LT -> goJust k kx x l
                                                            EQ -> Just (kx, x)
                                                            GT -> goJust k kx' x' r
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE lookupGE #-}
#else
{-# INLINE lookupGE #-}
#endif

{--------------------------------------------------------------------
  Construction
--------------------------------------------------------------------}
-- | /O(1)/. The empty map.
--
-- > empty      == fromList []
-- > size empty == 0
{-@ empty :: OMap k a @-}
empty :: Map k a
empty = Tip
{-# INLINE empty #-}

-- | /O(1)/. A map with a single element.
--
-- > singleton 1 'a'        == fromList [(1, 'a')]
-- > size (singleton 1 'a') == 1

{-@ singleton :: k -> a -> OMap k a @-}
singleton :: k -> a -> Map k a
singleton k x = Bin 1 k x Tip Tip
{-# INLINE singleton #-}

{--------------------------------------------------------------------
  Insertion
--------------------------------------------------------------------}
-- | /O(log n)/. Insert a new key and value in the map.
-- If the key is already present in the map, the associated value is
-- replaced with the supplied value. 'insert' is equivalent to
-- @'insertWith' 'const'@.
--
-- > insert 5 'x' (fromList [(5,'a'), (3,'b')]) == fromList [(3, 'b'), (5, 'x')]
-- > insert 7 'x' (fromList [(5,'a'), (3,'b')]) == fromList [(3, 'b'), (5, 'a'), (7, 'x')]
-- > insert 5 'x' empty                         == singleton 5 'x'

-- See Note: Type of local 'go' function
{-@ insert :: (Ord k) => k -> a -> OMap k a -> OMap k a @-}
insert :: Ord k => k -> a -> Map k a -> Map k a
insert = insert_go
--LIQUID insert = go
--LIQUID   where
--LIQUID     go :: Ord k => k -> a -> Map k a -> Map k a
--LIQUID     STRICT_1_OF_3(go)
--LIQUID     go kx x Tip = singleton kx x
--LIQUID     go kx x (Bin sz ky y l r) =
--LIQUID         case compare kx ky of
--LIQUID                   -- Bin ky y (go kx x l) r 
--LIQUID             LT -> balanceL ky y (go kx x l) r
--LIQUID             GT -> balanceR ky y l (go kx x r)
--LIQUID             EQ -> Bin sz kx x l r

{-@ insert_go :: (Ord k) => k -> a -> OMap k a -> OMap k a @-}
insert_go :: Ord k => k -> a -> Map k a -> Map k a
STRICT_1_OF_3(insert_go)
insert_go kx x Tip = singleton kx x
insert_go kx x (Bin sz ky y l r) =
    case compare kx ky of
              -- Bin ky y (insert_go kx x l) r 
        LT -> balanceL ky y (insert_go kx x l) r
        GT -> balanceR ky y l (insert_go kx x r)
        EQ -> Bin sz kx x l r
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE insert #-}
#else
{-# INLINE insert #-}
#endif

-- Insert a new key and value in the map if it is not already present.
-- Used by `union`.

-- See Note: Type of local 'go' function
insertR :: Ord k => k -> a -> Map k a -> Map k a
insertR = insertR_go
--LIQUID insertR = go
--LIQUID   where
--LIQUID     go :: Ord k => k -> a -> Map k a -> Map k a
--LIQUID     STRICT_1_OF_3(go)
--LIQUID     go kx x Tip = singleton kx x
--LIQUID     go kx x t@(Bin _ ky y l r) =
--LIQUID         case compare kx ky of
--LIQUID             LT -> balanceL ky y (go kx x l) r
--LIQUID             GT -> balanceR ky y l (go kx x r)
--LIQUID             EQ -> t

insertR_go :: Ord k => k -> a -> Map k a -> Map k a
STRICT_1_OF_3(insertR_go)
insertR_go kx x Tip = singleton kx x
insertR_go kx x t@(Bin _ ky y l r) =
    case compare kx ky of
        LT -> balanceL ky y (insertR_go kx x l) r
        GT -> balanceR ky y l (insertR_go kx x r)
        EQ -> t
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE insertR #-}
#else
{-# INLINE insertR #-}
#endif

-- | /O(log n)/. Insert with a function, combining new value and old value.
-- @'insertWith' f key value mp@
-- will insert the pair (key, value) into @mp@ if key does
-- not exist in the map. If the key does exist, the function will
-- insert the pair @(key, f new_value old_value)@.
--
-- > insertWith (++) 5 "xxx" (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "xxxa")]
-- > insertWith (++) 7 "xxx" (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "a"), (7, "xxx")]
-- > insertWith (++) 5 "xxx" empty                         == singleton 5 "xxx"

{-@ insertWith :: (Ord k) => (a -> a -> a) -> k -> a -> OMap k a -> OMap k a @-}
insertWith :: Ord k => (a -> a -> a) -> k -> a -> Map k a -> Map k a
insertWith f = insertWithKey (\_ x' y' -> f x' y')
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE insertWith #-}
#else
{-# INLINE insertWith #-}
#endif

-- | /O(log n)/. Insert with a function, combining key, new value and old value.
-- @'insertWithKey' f key value mp@
-- will insert the pair (key, value) into @mp@ if key does
-- not exist in the map. If the key does exist, the function will
-- insert the pair @(key,f key new_value old_value)@.
-- Note that the key passed to f is the same key passed to 'insertWithKey'.
--
-- > let f key new_value old_value = (show key) ++ ":" ++ new_value ++ "|" ++ old_value
-- > insertWithKey f 5 "xxx" (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "5:xxx|a")]
-- > insertWithKey f 7 "xxx" (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "a"), (7, "xxx")]
-- > insertWithKey f 5 "xxx" empty                         == singleton 5 "xxx"

-- See Note: Type of local 'go' function

{-@ insertWithKey :: (Ord k) => (k -> a -> a -> a) -> k -> a -> OMap k a -> OMap k a @-}
insertWithKey :: Ord k => (k -> a -> a -> a) -> k -> a -> Map k a -> Map k a
insertWithKey = insertWithKey_go
--LIQUID insertWithKey = go
--LIQUID   where
--LIQUID     go :: Ord k => (k -> a -> a -> a) -> k -> a -> Map k a -> Map k a
--LIQUID     STRICT_2_OF_4(go)
--LIQUID     go _ kx x Tip = singleton kx x
--LIQUID     go f kx x (Bin sy ky y l r) =
--LIQUID         case compare kx ky of
--LIQUID             LT -> balanceL ky y (go f kx x l) r
--LIQUID             GT -> balanceR ky y l (go f kx x r)
--LIQUID             EQ -> Bin sy kx (f kx x y) l r

{-@ insertWithKey_go :: (Ord k) => (k -> a -> a -> a) -> k -> a -> OMap k a -> OMap k a @-}
insertWithKey_go :: Ord k => (k -> a -> a -> a) -> k -> a -> Map k a -> Map k a
STRICT_2_OF_4(insertWithKey_go)
insertWithKey_go _ kx x Tip = singleton kx x
insertWithKey_go f kx x (Bin sy ky y l r) =
    case compare kx ky of
        LT -> balanceL ky y (insertWithKey_go f kx x l) r
        GT -> balanceR ky y l (insertWithKey_go f kx x r)
        EQ -> Bin sy kx (f kx x y) l r
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE insertWithKey #-}
#else
{-# INLINE insertWithKey #-}
#endif

-- | /O(log n)/. Combines insert operation with old value retrieval.
-- The expression (@'insertLookupWithKey' f k x map@)
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

-- See Note: Type of local 'go' function

{-@ insertLookupWithKey :: Ord k => (k -> a -> a -> a) -> k -> a -> OMap k a -> (Maybe a, OMap k a) @-}
insertLookupWithKey :: Ord k => (k -> a -> a -> a) -> k -> a -> Map k a -> (Maybe a, Map k a)
insertLookupWithKey = insertLookupWithKey_go
--LIQUID insertLookupWithKey = go
--LIQUID   where
--LIQUID     go :: Ord k => (k -> a -> a -> a) -> k -> a -> Map k a -> (Maybe a, Map k a)
--LIQUID     STRICT_2_OF_4(go)
--LIQUID     go _ kx x Tip = (Nothing, singleton kx x)
--LIQUID     go f kx x (Bin sy ky y l r) =
--LIQUID         case compare kx ky of
--LIQUID             LT -> let (found, l') = go f kx x l
--LIQUID                   in (found, balanceL ky y l' r)
--LIQUID             GT -> let (found, r') = go f kx x r
--LIQUID                   in (found, balanceR ky y l r')
--LIQUID             EQ -> (Just y, Bin sy kx (f kx x y) l r)

{-@ insertLookupWithKey_go :: Ord k => (k -> a -> a -> a) -> k -> a -> OMap k a -> (Maybe a, OMap k a) @-}
insertLookupWithKey_go :: Ord k => (k -> a -> a -> a) -> k -> a -> Map k a -> (Maybe a, Map k a)
STRICT_2_OF_4(insertLookupWithKey_go)
insertLookupWithKey_go _ kx x Tip = (Nothing, singleton kx x)
insertLookupWithKey_go f kx x (Bin sy ky y l r) =
    case compare kx ky of
        LT -> let (found, l') = insertLookupWithKey_go f kx x l
              in (found, balanceL ky y l' r)
        GT -> let (found, r') = insertLookupWithKey_go f kx x r
              in (found, balanceR ky y l r')
        EQ -> (Just y, Bin sy kx (f kx x y) l r)
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE insertLookupWithKey #-}
#else
{-# INLINE insertLookupWithKey #-}
#endif

{--------------------------------------------------------------------
  Deletion
--------------------------------------------------------------------}
-- | /O(log n)/. Delete a key and its value from the map. When the key is not
-- a member of the map, the original map is returned.
--
-- > delete 5 (fromList [(5,"a"), (3,"b")]) == singleton 3 "b"
-- > delete 7 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "a")]
-- > delete 5 empty                         == empty

-- See Note: Type of local 'go' function
{-@ delete :: (Ord k) => k -> OMap k a -> OMap k a @-}
delete :: Ord k => k -> Map k a -> Map k a
delete = delete_go
--LIQUID delete = go
--LIQUID   where
--LIQUID     go :: Ord k => k -> Map k a -> Map k a
--LIQUID     STRICT_1_OF_2(go)
--LIQUID     go _ Tip = Tip
--LIQUID     go k (Bin _ kx x l r) =
--LIQUID         case compare k kx of
--LIQUID             LT -> balanceR kx x (go k l) r
--LIQUID             GT -> balanceL kx x l (go k r)
--LIQUID             EQ -> glue kx l r

{-@ delete_go :: (Ord k) => k -> OMap k a -> OMap k a @-}
delete_go :: Ord k => k -> Map k a -> Map k a
STRICT_1_OF_2(delete_go)
delete_go _ Tip = Tip
delete_go k (Bin _ kx x l r) =
    case compare k kx of
        LT -> balanceR kx x (delete_go k l) r
        GT -> balanceL kx x l (delete_go k r)
        EQ -> glue kx l r
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE delete #-}
#else
{-# INLINE delete #-}
#endif

-- | /O(log n)/. Update a value at a specific key with the result of the provided function.
-- When the key is not
-- a member of the map, the original map is returned.
--
-- > adjust ("new " ++) 5 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "new a")]
-- > adjust ("new " ++) 7 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "a")]
-- > adjust ("new " ++) 7 empty                         == empty

{-@ adjust :: (Ord k) => (a -> a) -> k -> OMap k a -> OMap k a @-}
adjust :: Ord k => (a -> a) -> k -> Map k a -> Map k a
adjust f = adjustWithKey (\_ x -> f x)
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE adjust #-}
#else
{-# INLINE adjust #-}
#endif

-- | /O(log n)/. Adjust a value at a specific key. When the key is not
-- a member of the map, the original map is returned.
--
-- > let f key x = (show key) ++ ":new " ++ x
-- > adjustWithKey f 5 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "5:new a")]
-- > adjustWithKey f 7 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "a")]
-- > adjustWithKey f 7 empty                         == empty

{-@ adjustWithKey :: (Ord k) => (k -> a -> a) -> k -> OMap k a -> OMap k a @-}
adjustWithKey :: Ord k => (k -> a -> a) -> k -> Map k a -> Map k a
adjustWithKey f = updateWithKey (\k' x' -> Just (f k' x'))
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE adjustWithKey #-}
#else
{-# INLINE adjustWithKey #-}
#endif

-- | /O(log n)/. The expression (@'update' f k map@) updates the value @x@
-- at @k@ (if it is in the map). If (@f x@) is 'Nothing', the element is
-- deleted. If it is (@'Just' y@), the key @k@ is bound to the new value @y@.
--
-- > let f x = if x == "a" then Just "new a" else Nothing
-- > update f 5 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "new a")]
-- > update f 7 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "a")]
-- > update f 3 (fromList [(5,"a"), (3,"b")]) == singleton 5 "a"

{-@ update :: (Ord k) => (a -> Maybe a) -> k -> OMap k a -> OMap k a @-}
update :: Ord k => (a -> Maybe a) -> k -> Map k a -> Map k a
update f = updateWithKey (\_ x -> f x)
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE update #-}
#else
{-# INLINE update #-}
#endif

-- | /O(log n)/. The expression (@'updateWithKey' f k map@) updates the
-- value @x@ at @k@ (if it is in the map). If (@f k x@) is 'Nothing',
-- the element is deleted. If it is (@'Just' y@), the key @k@ is bound
-- to the new value @y@.
--
-- > let f k x = if x == "a" then Just ((show k) ++ ":new a") else Nothing
-- > updateWithKey f 5 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "5:new a")]
-- > updateWithKey f 7 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "a")]
-- > updateWithKey f 3 (fromList [(5,"a"), (3,"b")]) == singleton 5 "a"

-- See Note: Type of local 'go' function

{-@ updateWithKey :: (Ord k) => (k -> a -> Maybe a) -> k -> OMap k a -> OMap k a @-}
updateWithKey :: Ord k => (k -> a -> Maybe a) -> k -> Map k a -> Map k a
updateWithKey = updateWithKey_go
--LIQUID updateWithKey = go
--LIQUID   where
--LIQUID     go :: Ord k => (k -> a -> Maybe a) -> k -> Map k a -> Map k a
--LIQUID     STRICT_2_OF_3(go)
--LIQUID     go _ _ Tip = Tip
--LIQUID     go f k(Bin sx kx x l r) =
--LIQUID         case compare k kx of
--LIQUID            LT -> balanceR kx x (go f k l) r
--LIQUID            GT -> balanceL kx x l (go f k r)
--LIQUID            EQ -> case f kx x of
--LIQUID                    Just x' -> Bin sx kx x' l r
--LIQUID                    Nothing -> glue kx l r
{-@ updateWithKey_go :: (Ord k) => (k -> a -> Maybe a) -> k -> OMap k a -> OMap k a @-}
updateWithKey_go :: Ord k => (k -> a -> Maybe a) -> k -> Map k a -> Map k a
STRICT_2_OF_3(updateWithKey_go)
updateWithKey_go _ _ Tip = Tip
updateWithKey_go f k(Bin sx kx x l r) =
    case compare k kx of
       LT -> balanceR kx x (updateWithKey_go f k l) r
       GT -> balanceL kx x l (updateWithKey_go f k r)
       EQ -> case f kx x of
               Just x' -> Bin sx kx x' l r
               Nothing -> glue kx l r

#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE updateWithKey #-}
#else
{-# INLINE updateWithKey #-}
#endif

-- | /O(log n)/. Lookup and update. See also 'updateWithKey'.
-- The function returns changed value, if it is updated.
-- Returns the original key value if the map entry is deleted.
--
-- > let f k x = if x == "a" then Just ((show k) ++ ":new a") else Nothing
-- > updateLookupWithKey f 5 (fromList [(5,"a"), (3,"b")]) == (Just "5:new a", fromList [(3, "b"), (5, "5:new a")])
-- > updateLookupWithKey f 7 (fromList [(5,"a"), (3,"b")]) == (Nothing,  fromList [(3, "b"), (5, "a")])
-- > updateLookupWithKey f 3 (fromList [(5,"a"), (3,"b")]) == (Just "b", singleton 5 "a")

-- See Note: Type of local 'go' function

{-@ updateLookupWithKey :: (Ord k) => (k -> a -> Maybe a) -> k -> OMap k a -> (Maybe a, OMap k a) @-}
updateLookupWithKey :: Ord k => (k -> a -> Maybe a) -> k -> Map k a -> (Maybe a,Map k a)
updateLookupWithKey = updateLookupWithKey_go
--LIQUID updateLookupWithKey = go
--LIQUID  where
--LIQUID    go :: Ord k => (k -> a -> Maybe a) -> k -> Map k a -> (Maybe a,Map k a)
--LIQUID    STRICT_2_OF_3(go)
--LIQUID    go _ _ Tip = (Nothing,Tip)
--LIQUID    go f k (Bin sx kx x l r) =
--LIQUID           case compare k kx of
--LIQUID                LT -> let (found,l') = go f k l in (found,balanceR kx x l' r)
--LIQUID                GT -> let (found,r') = go f k r in (found,balanceL kx x l r')
--LIQUID                EQ -> case f kx x of
--LIQUID                        Just x' -> (Just x',Bin sx kx x' l r)
--LIQUID                        Nothing -> (Just x,glue kx l r)

{-@ updateLookupWithKey_go :: (Ord k) => (k -> a -> Maybe a) -> k -> OMap k a -> (Maybe a, OMap k a) @-}
updateLookupWithKey_go :: Ord k => (k -> a -> Maybe a) -> k -> Map k a -> (Maybe a,Map k a)
STRICT_2_OF_3(updateLookupWithKey_go)
updateLookupWithKey_go _ _ Tip = (Nothing,Tip)
updateLookupWithKey_go f k (Bin sx kx x l r) =
       case compare k kx of
            LT -> let (found,l') = updateLookupWithKey_go f k l in (found,balanceR kx x l' r)
            GT -> let (found,r') = updateLookupWithKey_go f k r in (found,balanceL kx x l r')
            EQ -> case f kx x of
                    Just x' -> (Just x',Bin sx kx x' l r)
                    Nothing -> (Just x,glue kx l r)

#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE updateLookupWithKey #-}
#else
{-# INLINE updateLookupWithKey #-}
#endif

-- | /O(log n)/. The expression (@'alter' f k map@) alters the value @x@ at @k@, or absence thereof.
-- 'alter' can be used to insert, delete, or update a value in a 'Map'.
-- In short : @'lookup' k ('alter' f k m) = f ('lookup' k m)@.
--
-- > let f _ = Nothing
-- > alter f 7 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "a")]
-- > alter f 5 (fromList [(5,"a"), (3,"b")]) == singleton 3 "b"
-- >
-- > let f _ = Just "c"
-- > alter f 7 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "a"), (7, "c")]
-- > alter f 5 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "c")]

-- See Note: Type of local 'go' function

{-@ alter :: (Ord k) => (Maybe a -> Maybe a) -> k -> OMap k a -> OMap k a @-}
alter :: Ord k => (Maybe a -> Maybe a) -> k -> Map k a -> Map k a
alter = alter_go
--LIQUID alter = go
--LIQUID  where
--LIQUID    go :: Ord k => (Maybe a -> Maybe a) -> k -> Map k a -> Map k a
--LIQUID    STRICT_2_OF_3(go)
--LIQUID    go f k Tip = case f Nothing of
--LIQUID               Nothing -> Tip
--LIQUID               Just x  -> singleton k x
--LIQUID
--LIQUID    go f k (Bin sx kx x l r) = case compare k kx of
--LIQUID               LT -> balance kx x (go f k l) r
--LIQUID               GT -> balance kx x l (go f k r)
--LIQUID               EQ -> case f (Just x) of
--LIQUID                       Just x' -> Bin sx kx x' l r
--LIQUID                       Nothing -> glue kx l r

alter_go :: Ord k => (Maybe a -> Maybe a) -> k -> Map k a -> Map k a
STRICT_2_OF_3(alter_go)
alter_go f k Tip = case f Nothing of
           Nothing -> Tip
           Just x  -> singleton k x

alter_go f k (Bin sx kx x l r) = case compare k kx of
           LT -> balance kx x (alter_go f k l) r
           GT -> balance kx x l (alter_go f k r)
           EQ -> case f (Just x) of
                   Just x' -> Bin sx kx x' l r
                   Nothing -> glue kx l r

#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE alter #-}
#else
{-# INLINE alter #-}
#endif

{--------------------------------------------------------------------
  Indexing
--------------------------------------------------------------------}
-- | /O(log n)/. Return the /index/ of a key. The index is a number from
-- /0/ up to, but not including, the 'size' of the map. Calls 'error' when
-- the key is not a 'member' of the map.
--
-- > findIndex 2 (fromList [(5,"a"), (3,"b")])    Error: element is not in the map
-- > findIndex 3 (fromList [(5,"a"), (3,"b")]) == 0
-- > findIndex 5 (fromList [(5,"a"), (3,"b")]) == 1
-- > findIndex 6 (fromList [(5,"a"), (3,"b")])    Error: element is not in the map

-- See Note: Type of local 'go' function

{-@ findIndex :: (Ord k) => k -> OMap k a -> GHC.Types.Int @-}
findIndex :: Ord k => k -> Map k a -> Int
findIndex = findIndex_go 0
--LIQUID findIndex = go 0
--LIQUID   where
--LIQUID     go :: Ord k => Int -> k -> Map k a -> Int
--LIQUID     STRICT_1_OF_3(go)
--LIQUID     STRICT_2_OF_3(go)
--LIQUID     go _   _ Tip  = error "Map.findIndex: element is not in the map"
--LIQUID     go idx k (Bin _ kx _ l r) = case compare k kx of
--LIQUID       LT -> go idx k l
--LIQUID       GT -> go (idx + size l + 1) k r
--LIQUID       EQ -> idx + size l

{-@ findIndex_go :: (Ord k) => Int -> k -> OMap k a -> GHC.Types.Int @-}
{-@ Decrease findIndex_go 4 @-}
findIndex_go :: Ord k => Int -> k -> Map k a -> Int
STRICT_1_OF_3(findIndex_go)
STRICT_2_OF_3(findIndex_go)
findIndex_go _   _ Tip  = error "Map.findIndex: element is not in the map"
findIndex_go idx k (Bin _ kx _ l r) = case compare k kx of
  LT -> findIndex_go idx k l
  GT -> findIndex_go (idx + size l + 1) k r
  EQ -> idx + size l
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE findIndex #-}
#endif

-- | /O(log n)/. Lookup the /index/ of a key. The index is a number from
-- /0/ up to, but not including, the 'size' of the map.
--
-- > isJust (lookupIndex 2 (fromList [(5,"a"), (3,"b")]))   == False
-- > fromJust (lookupIndex 3 (fromList [(5,"a"), (3,"b")])) == 0
-- > fromJust (lookupIndex 5 (fromList [(5,"a"), (3,"b")])) == 1
-- > isJust (lookupIndex 6 (fromList [(5,"a"), (3,"b")]))   == False

-- See Note: Type of local 'go' function
{-@ lookupIndex :: (Ord k) => k -> OMap k a -> Maybe GHC.Types.Int @-}
lookupIndex :: Ord k => k -> Map k a -> Maybe Int
lookupIndex = lookupIndex_go 0
--LIQUID lookupIndex = go 0
--LIQUID   where
--LIQUID     go :: Ord k => Int -> k -> Map k a -> Maybe Int
--LIQUID     STRICT_1_OF_3(go)
--LIQUID     STRICT_2_OF_3(go)
--LIQUID     go _   _ Tip  = Nothing
--LIQUID     go idx k (Bin _ kx _ l r) = case compare k kx of
--LIQUID       LT -> go idx k l
--LIQUID       GT -> go (idx + size l + 1) k r
--LIQUID       EQ -> Just $! idx + size l

{-@ lookupIndex_go :: (Ord k) => Int -> k -> OMap k a -> Maybe GHC.Types.Int @-}
{-@ Decrease lookupIndex_go 4 @-}
lookupIndex_go :: Ord k => Int -> k -> Map k a -> Maybe Int
STRICT_1_OF_3(lookupIndex_go)
STRICT_2_OF_3(lookupIndex_go)
lookupIndex_go _   _ Tip  = Nothing
lookupIndex_go idx k (Bin _ kx _ l r) = case compare k kx of
  LT -> lookupIndex_go idx k l
  GT -> lookupIndex_go (idx + size l + 1) k r
  EQ -> Just $! idx + size l
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE lookupIndex #-}
#endif

-- | /O(log n)/. Retrieve an element by /index/. Calls 'error' when an
-- invalid index is used.
--
-- > elemAt 0 (fromList [(5,"a"), (3,"b")]) == (3,"b")
-- > elemAt 1 (fromList [(5,"a"), (3,"b")]) == (5, "a")
-- > elemAt 2 (fromList [(5,"a"), (3,"b")])    Error: index out of range


{-@ elemAt :: GHC.Types.Int -> OMap k a -> (k, a) @-}
{-@ Decrease elemAt 2 @-}
elemAt :: Int -> Map k a -> (k,a)
STRICT_1_OF_2(elemAt)
elemAt _ Tip = error "Map.elemAt: index out of range"
elemAt i (Bin _ kx x l r)
  = case compare i sizeL of
      LT -> elemAt i l
      GT -> elemAt (i-sizeL-1) r
      EQ -> (kx,x)
  where
    sizeL = size l

-- | /O(log n)/. Update the element at /index/. Calls 'error' when an
-- invalid index is used.
--
-- > updateAt (\ _ _ -> Just "x") 0    (fromList [(5,"a"), (3,"b")]) == fromList [(3, "x"), (5, "a")]
-- > updateAt (\ _ _ -> Just "x") 1    (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "x")]
-- > updateAt (\ _ _ -> Just "x") 2    (fromList [(5,"a"), (3,"b")])    Error: index out of range
-- > updateAt (\ _ _ -> Just "x") (-1) (fromList [(5,"a"), (3,"b")])    Error: index out of range
-- > updateAt (\_ _  -> Nothing)  0    (fromList [(5,"a"), (3,"b")]) == singleton 5 "a"
-- > updateAt (\_ _  -> Nothing)  1    (fromList [(5,"a"), (3,"b")]) == singleton 3 "b"
-- > updateAt (\_ _  -> Nothing)  2    (fromList [(5,"a"), (3,"b")])    Error: index out of range
-- > updateAt (\_ _  -> Nothing)  (-1) (fromList [(5,"a"), (3,"b")])    Error: index out of range

{-@ updateAt :: (k -> a -> Maybe a) -> GHC.Types.Int -> OMap k a -> OMap k a @-}
{-@ Decrease updateAt 3 @-}
updateAt :: (k -> a -> Maybe a) -> Int -> Map k a -> Map k a
updateAt f i t = i `seq`
  case t of
    Tip -> error "Map.updateAt: index out of range"
    Bin sx kx x l r -> case compare i sizeL of
      LT -> balanceR kx x (updateAt f i l) r
      GT -> balanceL kx x l (updateAt f (i-sizeL-1) r)
      EQ -> case f kx x of
              Just x' -> Bin sx kx x' l r
              Nothing -> glue kx l r
      where
        sizeL = size l

-- | /O(log n)/. Delete the element at /index/.
-- Defined as (@'deleteAt' i map = 'updateAt' (\k x -> 'Nothing') i map@).
--
-- > deleteAt 0  (fromList [(5,"a"), (3,"b")]) == singleton 5 "a"
-- > deleteAt 1  (fromList [(5,"a"), (3,"b")]) == singleton 3 "b"
-- > deleteAt 2 (fromList [(5,"a"), (3,"b")])     Error: index out of range
-- > deleteAt (-1) (fromList [(5,"a"), (3,"b")])  Error: index out of range

{-@ deleteAt :: GHC.Types.Int -> OMap k a -> OMap k a @-}
{-@ Decrease deleteAt 2 @-}
deleteAt :: Int -> Map k a -> Map k a
deleteAt i t = i `seq`
  case t of
    Tip -> error "Map.deleteAt: index out of range"
    Bin _ kx x l r -> case compare i sizeL of
      LT -> balanceR kx x (deleteAt i l) r
      GT -> balanceL kx x l (deleteAt (i-sizeL-1) r)
      EQ -> glue kx l r
      where
        sizeL = size l


{--------------------------------------------------------------------
  Minimal, Maximal
--------------------------------------------------------------------}
-- | /O(log n)/. The minimal key of the map. Calls 'error' if the map is empty.
--
-- > findMin (fromList [(5,"a"), (3,"b")]) == (3,"b")
-- > findMin empty                            Error: empty map has no minimal element

{-@ findMin :: OMap k a -> (k, a) @-}
findMin :: Map k a -> (k,a)
findMin (Bin _ kx x Tip _)  = (kx,x)
findMin (Bin _ _  _ l _)    = findMin l
findMin Tip                 = error "Map.findMin: empty map has no minimal element"

-- | /O(log n)/. The maximal key of the map. Calls 'error' if the map is empty.
--
-- > findMax (fromList [(5,"a"), (3,"b")]) == (5,"a")
-- > findMax empty                            Error: empty map has no maximal element

{-@ findMax :: OMap k a -> (k, a) @-}
findMax :: Map k a -> (k,a)
findMax (Bin _ kx x _ Tip)  = (kx,x)
findMax (Bin _ _  _ _ r)    = findMax r
findMax Tip                 = error "Map.findMax: empty map has no maximal element"

-- | /O(log n)/. Delete the minimal key. Returns an empty map if the map is empty.
--
-- > deleteMin (fromList [(5,"a"), (3,"b"), (7,"c")]) == fromList [(5,"a"), (7,"c")]
-- > deleteMin empty == empty


{-@ deleteMin :: OMap k a -> OMap k a @-}
deleteMin :: Map k a -> Map k a
deleteMin (Bin _ _  _ Tip r)  = r
deleteMin (Bin _ kx x l r)    = balanceR kx x (deleteMin l) r
deleteMin Tip                 = Tip

-- | /O(log n)/. Delete the maximal key. Returns an empty map if the map is empty.
--
-- > deleteMax (fromList [(5,"a"), (3,"b"), (7,"c")]) == fromList [(3,"b"), (5,"a")]
-- > deleteMax empty == empty

{-@ deleteMax :: OMap k a -> OMap k a @-}
deleteMax :: Map k a -> Map k a
deleteMax (Bin _ _  _ l Tip)  = l
deleteMax (Bin _ kx x l r)    = balanceL kx x l (deleteMax r)
deleteMax Tip                 = Tip

-- | /O(log n)/. Update the value at the minimal key.
--
-- > updateMin (\ a -> Just ("X" ++ a)) (fromList [(5,"a"), (3,"b")]) == fromList [(3, "Xb"), (5, "a")]
-- > updateMin (\ _ -> Nothing)         (fromList [(5,"a"), (3,"b")]) == singleton 5 "a"

{-@ updateMin :: (a -> Maybe a) -> OMap k a -> OMap k a @-}
updateMin :: (a -> Maybe a) -> Map k a -> Map k a
updateMin f m
  = updateMinWithKey (\_ x -> f x) m

-- | /O(log n)/. Update the value at the maximal key.
--
-- > updateMax (\ a -> Just ("X" ++ a)) (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "Xa")]
-- > updateMax (\ _ -> Nothing)         (fromList [(5,"a"), (3,"b")]) == singleton 3 "b"

{-@ updateMax :: (a -> Maybe a) -> OMap k a -> OMap k a @-}
updateMax :: (a -> Maybe a) -> Map k a -> Map k a
updateMax f m
  = updateMaxWithKey (\_ x -> f x) m


-- | /O(log n)/. Update the value at the minimal key.
--
-- > updateMinWithKey (\ k a -> Just ((show k) ++ ":" ++ a)) (fromList [(5,"a"), (3,"b")]) == fromList [(3,"3:b"), (5,"a")]
-- > updateMinWithKey (\ _ _ -> Nothing)                     (fromList [(5,"a"), (3,"b")]) == singleton 5 "a"

{-@ updateMinWithKey :: (k -> a -> Maybe a) -> OMap k a -> OMap k a @-}
updateMinWithKey :: (k -> a -> Maybe a) -> Map k a -> Map k a
updateMinWithKey _ Tip                 = Tip
updateMinWithKey f (Bin sx kx x Tip r) = case f kx x of
                                           Nothing -> r
                                           Just x' -> Bin sx kx x' Tip r
updateMinWithKey f (Bin _ kx x l r)    = balanceR kx x (updateMinWithKey f l) r

-- | /O(log n)/. Update the value at the maximal key.
--
-- > updateMaxWithKey (\ k a -> Just ((show k) ++ ":" ++ a)) (fromList [(5,"a"), (3,"b")]) == fromList [(3,"b"), (5,"5:a")]
-- > updateMaxWithKey (\ _ _ -> Nothing)                     (fromList [(5,"a"), (3,"b")]) == singleton 3 "b"

{-@ updateMaxWithKey :: (k -> a -> Maybe a) -> OMap k a -> OMap k a @-}
updateMaxWithKey :: (k -> a -> Maybe a) -> Map k a -> Map k a
updateMaxWithKey _ Tip                 = Tip
updateMaxWithKey f (Bin sx kx x l Tip) = case f kx x of
                                           Nothing -> l
                                           Just x' -> Bin sx kx x' l Tip
updateMaxWithKey f (Bin _ kx x l r)    = balanceL kx x l (updateMaxWithKey f r)

-- | /O(log n)/. Retrieves the minimal (key,value) pair of the map, and
-- the map stripped of that element, or 'Nothing' if passed an empty map.
--
-- > minViewWithKey (fromList [(5,"a"), (3,"b")]) == Just ((3,"b"), singleton 5 "a")
-- > minViewWithKey empty == Nothing

{-@ minViewWithKey :: OMap k a -> Maybe (k, a, OMap k a) @-}
minViewWithKey :: Map k a -> Maybe (k, a, Map k a)
minViewWithKey Tip = Nothing
minViewWithKey x   = Just (deleteFindMin x)

-- | /O(log n)/. Retrieves the maximal (key,value) pair of the map, and
-- the map stripped of that element, or 'Nothing' if passed an empty map.
--
-- > maxViewWithKey (fromList [(5,"a"), (3,"b")]) == Just ((5,"a"), singleton 3 "b")
-- > maxViewWithKey empty == Nothing

{-@ maxViewWithKey :: OMap k a -> Maybe (k, a, OMap k a) @-}
maxViewWithKey :: Map k a -> Maybe (k, a, Map k a)
maxViewWithKey Tip = Nothing
maxViewWithKey x   = Just (deleteFindMax x)

-- | /O(log n)/. Retrieves the value associated with minimal key of the
-- map, and the map stripped of that element, or 'Nothing' if passed an
-- empty map.
--
-- > minView (fromList [(5,"a"), (3,"b")]) == Just ("b", singleton 5 "a")
-- > minView empty == Nothing

{-@ minView :: OMap k a -> Maybe (a, OMap k a) @-}
minView :: Map k a -> Maybe (a, Map k a)
minView Tip = Nothing
minView x   = let (_, m, t) = deleteFindMin x in Just (m ,t) -- (first snd $ deleteFindMin x)

-- | /O(log n)/. Retrieves the value associated with maximal key of the
-- map, and the map stripped of that element, or 'Nothing' if passed an
--
-- > maxView (fromList [(5,"a"), (3,"b")]) == Just ("a", singleton 3 "b")
-- > maxView empty == Nothing

{-@ maxView :: OMap k a -> Maybe (a, OMap k a) @-}
maxView :: Map k a -> Maybe (a, Map k a)
maxView Tip = Nothing
maxView x   = let (_, m, t) = deleteFindMax x in Just (m, t)

-- Update the 1st component of a tuple (special case of Control.Arrow.first)
first :: (a -> b) -> (a, c) -> (b, c)
first f (x, y) = (f x, y)

{--------------------------------------------------------------------
  Union.
--------------------------------------------------------------------}
-- | The union of a list of maps:
--   (@'unions' == 'Prelude.foldl' 'union' 'empty'@).
--
-- > unions [(fromList [(5, "a"), (3, "b")]), (fromList [(5, "A"), (7, "C")]), (fromList [(5, "A3"), (3, "B3")])]
-- >     == fromList [(3, "b"), (5, "a"), (7, "C")]
-- > unions [(fromList [(5, "A3"), (3, "B3")]), (fromList [(5, "A"), (7, "C")]), (fromList [(5, "a"), (3, "b")])]
-- >     == fromList [(3, "B3"), (5, "A3"), (7, "C")]

{-@ unions :: (Ord k) => [OMap k a] -> OMap k a @-}
unions :: Ord k => [Map k a] -> Map k a
unions ts
  = foldlStrict union empty ts
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE unions #-}
#endif

-- | The union of a list of maps, with a combining operation:
--   (@'unionsWith' f == 'Prelude.foldl' ('unionWith' f) 'empty'@).
--
-- > unionsWith (++) [(fromList [(5, "a"), (3, "b")]), (fromList [(5, "A"), (7, "C")]), (fromList [(5, "A3"), (3, "B3")])]
-- >     == fromList [(3, "bB3"), (5, "aAA3"), (7, "C")]

{-@ unionsWith :: (Ord k) => (a->a->a) -> [OMap k a] -> OMap k a @-}
unionsWith :: Ord k => (a->a->a) -> [Map k a] -> Map k a
unionsWith f ts
  = foldlStrict (unionWith f) empty ts
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE unionsWith #-}
#endif

-- | /O(n+m)/.
-- The expression (@'union' t1 t2@) takes the left-biased union of @t1@ and @t2@.
-- It prefers @t1@ when duplicate keys are encountered,
-- i.e. (@'union' == 'unionWith' 'const'@).
-- The implementation uses the efficient /hedge-union/ algorithm.
-- Hedge-union is more efficient on (bigset \``union`\` smallset).
--
-- > union (fromList [(5, "a"), (3, "b")]) (fromList [(5, "A"), (7, "C")]) == fromList [(3, "b"), (5, "a"), (7, "C")]
 
{-@ union :: (Ord k) => OMap k a -> OMap k a -> OMap k a @-}
union :: Ord k => Map k a -> Map k a -> Map k a
union Tip t2  = t2
union t1 Tip  = t1
union t1 t2 = hedgeUnion NothingS NothingS t1 t2
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE union #-}
#endif

-- left-biased hedge union
{-@ hedgeUnion :: (Ord k) => lo: MaybeS k 
                          -> hi: MaybeS {v: k | (IfDefLt lo v) }               
                          -> OMap {v: k | (KeyBetween lo hi v) } a 
                          -> {v: OMap k a | (RootBetween lo hi v) }                       
                          ->  OMap {v: k | (KeyBetween lo hi v)} a @-}
hedgeUnion :: Ord a => MaybeS a -> MaybeS a -> Map a b -> Map a b -> Map a b
hedgeUnion _   _   t1  Tip = t1
hedgeUnion blo bhi Tip (Bin _ kx x l r) = join kx x (filterGt blo l) (filterLt bhi r)
hedgeUnion _   _   t1  (Bin _ kx x Tip Tip) = insertR kx x t1 -- According to benchmarks, this special case increases
                                                              -- performance up to 30%. It does not help in difference or intersection.
hedgeUnion blo bhi (Bin _ kx x l r) t2 = join kx x (hedgeUnion blo bmi l (trim blo bmi t2))
                                                   (hedgeUnion bmi bhi r (trim bmi bhi t2))
  where bmi = JustS kx
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE hedgeUnion #-}
#endif

{--------------------------------------------------------------------
  Union with a combining function
--------------------------------------------------------------------}
-- | /O(n+m)/. Union with a combining function. The implementation uses the efficient /hedge-union/ algorithm.
--
-- > unionWith (++) (fromList [(5, "a"), (3, "b")]) (fromList [(5, "A"), (7, "C")]) == fromList [(3, "b"), (5, "aA"), (7, "C")]

{-@ unionWith :: (Ord k) => (a -> a -> a) -> OMap k a -> OMap k a -> OMap k a @-}
unionWith :: Ord k => (a -> a -> a) -> Map k a -> Map k a -> Map k a
unionWith f m1 m2
  = unionWithKey (\_ x y -> f x y) m1 m2
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE unionWith #-}
#endif

-- | /O(n+m)/.
-- Union with a combining function. The implementation uses the efficient /hedge-union/ algorithm.
-- Hedge-union is more efficient on (bigset \``union`\` smallset).
--
-- > let f key left_value right_value = (show key) ++ ":" ++ left_value ++ "|" ++ right_value
-- > unionWithKey f (fromList [(5, "a"), (3, "b")]) (fromList [(5, "A"), (7, "C")]) == fromList [(3, "b"), (5, "5:a|A"), (7, "C")]

{-@ unionWithKey :: (Ord k) => (k -> a -> a -> a) -> OMap k a -> OMap k a -> OMap k a @-}
unionWithKey :: Ord k => (k -> a -> a -> a) -> Map k a -> Map k a -> Map k a
unionWithKey f t1 t2 = mergeWithKey (\k x1 x2 -> Just $ f k x1 x2) (\ _ _ x -> x) (\ _ _ x -> x) t1 t2
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE unionWithKey #-}
#endif

{--------------------------------------------------------------------
  Difference
--------------------------------------------------------------------}
-- | /O(n+m)/. Difference of two maps.
-- Return elements of the first map not existing in the second map.
-- The implementation uses an efficient /hedge/ algorithm comparable with /hedge-union/.
--
-- > difference (fromList [(5, "a"), (3, "b")]) (fromList [(5, "A"), (7, "C")]) == singleton 3 "b"

{-@ difference :: (Ord k) => OMap k a -> OMap k b -> OMap k a @-}
difference :: Ord k => Map k a -> Map k b -> Map k a
difference Tip _   = Tip
difference t1 Tip  = t1
difference t1 t2   = hedgeDiff NothingS NothingS t1 t2
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE difference #-}
#endif

{-@ hedgeDiff  :: (Ord k) => lo: MaybeS k  
                          -> hi: MaybeS {v: k | (IfDefLt lo v) }               
                          -> {v: OMap k a | (RootBetween lo hi v) }                       
                          -> OMap {v: k | (KeyBetween lo hi v) } b 
                          -> OMap {v: k | (KeyBetween lo hi v) } a @-}
{-@ Decrease hedgeDiff 5 @-}
hedgeDiff :: Ord a => MaybeS a -> MaybeS a -> Map a b -> Map a c -> Map a b
hedgeDiff _  _   Tip _                  = Tip
hedgeDiff blo bhi (Bin _ kx x l r) Tip  = join kx x (filterGt blo l) (filterLt bhi r)
hedgeDiff blo bhi t (Bin _ kx _ l r)    = merge kx (hedgeDiff blo bmi (trim blo bmi t) l)
                                                   (hedgeDiff bmi bhi (trim bmi bhi t) r)
  where bmi = JustS kx
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE hedgeDiff #-}
#endif

-- | /O(n+m)/. Difference with a combining function.
-- When two equal keys are
-- encountered, the combining function is applied to the values of these keys.
-- If it returns 'Nothing', the element is discarded (proper set difference). If
-- it returns (@'Just' y@), the element is updated with a new value @y@.
-- The implementation uses an efficient /hedge/ algorithm comparable with /hedge-union/.
--
-- > let f al ar = if al == "b" then Just (al ++ ":" ++ ar) else Nothing
-- > differenceWith f (fromList [(5, "a"), (3, "b")]) (fromList [(5, "A"), (3, "B"), (7, "C")])
-- >     == singleton 3 "b:B"

{-@ differenceWith :: (Ord k) => (a -> b -> Maybe a) -> OMap k a -> OMap k b -> OMap k a @-}
differenceWith :: Ord k => (a -> b -> Maybe a) -> Map k a -> Map k b -> Map k a
differenceWith f m1 m2
  = differenceWithKey (\_ x y -> f x y) m1 m2
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE differenceWith #-}
#endif

-- | /O(n+m)/. Difference with a combining function. When two equal keys are
-- encountered, the combining function is applied to the key and both values.
-- If it returns 'Nothing', the element is discarded (proper set difference). If
-- it returns (@'Just' y@), the element is updated with a new value @y@.
-- The implementation uses an efficient /hedge/ algorithm comparable with /hedge-union/.
--
-- > let f k al ar = if al == "b" then Just ((show k) ++ ":" ++ al ++ "|" ++ ar) else Nothing
-- > differenceWithKey f (fromList [(5, "a"), (3, "b")]) (fromList [(5, "A"), (3, "B"), (10, "C")])
-- >     == singleton 3 "3:b|B"

{-@ differenceWithKey :: (Ord k) => (k -> a -> b -> Maybe a) -> OMap k a -> OMap k b -> OMap k a @-}
differenceWithKey :: Ord k => (k -> a -> b -> Maybe a) -> Map k a -> Map k b -> Map k a
differenceWithKey f t1 t2 = mergeWithKey f (\_ _ x -> x) (\ _ _ _ -> Tip) t1 t2
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE differenceWithKey #-}
#endif


{--------------------------------------------------------------------
  Intersection
--------------------------------------------------------------------}
-- | /O(n+m)/. Intersection of two maps.
-- Return data in the first map for the keys existing in both maps.
-- (@'intersection' m1 m2 == 'intersectionWith' 'const' m1 m2@).
--
-- > intersection (fromList [(5, "a"), (3, "b")]) (fromList [(5, "A"), (7, "C")]) == singleton 5 "a"

{-@ intersection :: (Ord k) => OMap k a -> OMap k b -> OMap k a @-}
intersection :: Ord k => Map k a -> Map k b -> Map k a
intersection Tip _ = Tip
intersection _ Tip = Tip
intersection t1 t2 = hedgeInt NothingS NothingS t1 t2
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE intersection #-}
#endif

{-@ hedgeInt   :: (Ord k) => lo: MaybeS k 
                          -> hi: MaybeS {v: k | (IfDefLt lo v) }               
                          -> OMap {v: k | (KeyBetween lo hi v) } a 
                          -> {v: OMap k b | (RootBetween lo hi v) }                       
                          ->  OMap {v: k | (KeyBetween lo hi v)} a @-}

hedgeInt :: Ord k => MaybeS k -> MaybeS k -> Map k a -> Map k b -> Map k a
hedgeInt _ _ _   Tip = Tip
hedgeInt _ _ Tip _   = Tip
hedgeInt blo bhi (Bin _ kx x l r) t2 = let l' = hedgeInt blo bmi l (trim blo bmi t2)
                                           r' = hedgeInt bmi bhi r (trim bmi bhi t2)
                                       in if kx `member` t2 then join kx x l' r' else merge kx l' r'
  where bmi = JustS kx

#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE hedgeInt #-}
#endif

-- | /O(n+m)/. Intersection with a combining function.
--
-- > intersectionWith (++) (fromList [(5, "a"), (3, "b")]) (fromList [(5, "A"), (7, "C")]) == singleton 5 "aA"

{-@ intersectionWith :: (Ord k) => (a -> b -> c) -> OMap k a -> OMap k b -> OMap k c @-}
intersectionWith :: Ord k => (a -> b -> c) -> Map k a -> Map k b -> Map k c
intersectionWith f m1 m2
  = intersectionWithKey (\_ x y -> f x y) m1 m2
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE intersectionWith #-}
#endif

-- | /O(n+m)/. Intersection with a combining function.
-- Intersection is more efficient on (bigset \``intersection`\` smallset).
--
-- > let f k al ar = (show k) ++ ":" ++ al ++ "|" ++ ar
-- > intersectionWithKey f (fromList [(5, "a"), (3, "b")]) (fromList [(5, "A"), (7, "C")]) == singleton 5 "5:a|A"


{-@ intersectionWithKey :: (Ord k) => (k -> a -> b -> c) -> OMap k a -> OMap k b -> OMap k c @-}
intersectionWithKey :: Ord k => (k -> a -> b -> c) -> Map k a -> Map k b -> Map k c
intersectionWithKey f t1 t2 = mergeWithKey (\k x1 x2 -> Just $ f k x1 x2) (\ _ _ _ -> Tip) (\ _ _ _ -> Tip) t1 t2
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE intersectionWithKey #-}
#endif


{--------------------------------------------------------------------
  MergeWithKey
--------------------------------------------------------------------}

-- | /O(n+m)/. A high-performance universal combining function. This function
-- is used to define 'unionWith', 'unionWithKey', 'differenceWith',
-- 'differenceWithKey', 'intersectionWith', 'intersectionWithKey' and can be
-- used to define other custom combine functions.
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
-- The values can be modified arbitrarily. Most common variants of @only1@ and
-- @only2@ are 'id' and @'const' 'empty'@, but for example @'map' f@ or
-- @'filterWithKey' f@ could be used for any @f@.

{-@ mergeWithKey :: (Ord k) => (k -> a -> b -> Maybe c) 
                          -> (lo:MaybeS k -> hi: MaybeS k -> OMap {v: k | (KeyBetween lo hi v) } a -> OMap {v: k | (KeyBetween lo hi v) } c) 
                          -> (lo:MaybeS k -> hi: MaybeS k -> OMap {v: k | (KeyBetween lo hi v) } b -> OMap {v: k | (KeyBetween lo hi v) } c)
                          -> OMap k a -> OMap k b -> OMap k c @-}
mergeWithKey :: Ord k => (k -> a -> b -> Maybe c) -> (MaybeS k -> MaybeS k -> Map k a -> Map k c) -> (MaybeS k -> MaybeS k -> Map k b -> Map k c)
             -> Map k a -> Map k b -> Map k c
mergeWithKey f g1 g2 = go
  where
    go Tip t2 = g2 NothingS NothingS t2
    go t1 Tip = g1 NothingS NothingS t1
    go t1 t2  = hedgeMerge f g1 g2 NothingS NothingS t1 t2

{-@ hedgeMerge :: (Ord k) => (k -> a -> b -> Maybe c) 
                          -> (lo:MaybeS k -> hi: MaybeS k -> OMap {v: k | (KeyBetween lo hi v) } a -> OMap {v: k | (KeyBetween lo hi v) } c)
                          -> (lo:MaybeS k -> hi: MaybeS k -> OMap {v: k | (KeyBetween lo hi v) } b -> OMap {v: k | (KeyBetween lo hi v) } c)
                          -> lo: MaybeS k 
                          -> hi: MaybeS {v: k | (IfDefLt lo v) }               
                          -> OMap {v: k | (KeyBetween lo hi v) } a 
                          -> {v: OMap k b | (RootBetween lo hi v) }                       
                          ->  OMap {v: k | (KeyBetween lo hi v)} c @-}

hedgeMerge :: Ord k => (k -> a -> b -> Maybe c) 
                    -> (MaybeS k -> MaybeS k -> Map k a -> Map k c) 
                    -> (MaybeS k -> MaybeS k -> Map k b -> Map k c)
                    -> MaybeS k -> MaybeS k 
                    -> Map k a -> Map k b -> Map k c
hedgeMerge f g1 g2 blo bhi   t1  Tip 
  = g1 blo bhi t1
hedgeMerge f g1 g2 blo bhi Tip (Bin _ kx x l r) 
  = g2 blo bhi $ join kx x (filterGt blo l) (filterLt bhi r)
hedgeMerge f g1 g2 blo bhi (Bin _ kx x l r) t2  
  = let bmi = JustS kx 
        l' = hedgeMerge f g1 g2 blo bmi l (trim blo bmi t2)
        (found, trim_t2) = trimLookupLo kx bhi t2
        r' = hedgeMerge f g1 g2 bmi bhi r trim_t2
    in case found of
         Nothing -> case g1 blo bhi (singleton kx x) of
                      Tip -> merge kx l' r'
                      (Bin _ _ x' Tip Tip) -> join kx x' l' r'
                      _ -> error "mergeWithKey: Given function only1 does not fulfil required conditions (see documentation)"
         Just x2 -> case f kx x x2 of
                      Nothing -> merge kx l' r'
                      Just x' -> join kx x' l' r'
{-# INLINE mergeWithKey #-}

{--------------------------------------------------------------------
  Submap
--------------------------------------------------------------------}
-- | /O(n+m)/.
-- This function is defined as (@'isSubmapOf' = 'isSubmapOfBy' (==)@).
--
{-@ isSubmapOf :: (Ord k, Eq a) => OMap k a -> OMap k a -> Bool @-}
isSubmapOf :: (Ord k,Eq a) => Map k a -> Map k a -> Bool
isSubmapOf m1 m2 = isSubmapOfBy (==) m1 m2
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE isSubmapOf #-}
#endif

{- | /O(n+m)/.
 The expression (@'isSubmapOfBy' f t1 t2@) returns 'True' if
 all keys in @t1@ are in tree @t2@, and when @f@ returns 'True' when
 applied to their respective values. For example, the following
 expressions are all 'True':

 > isSubmapOfBy (==) (fromList [('a',1)]) (fromList [('a',1),('b',2)])
 > isSubmapOfBy (<=) (fromList [('a',1)]) (fromList [('a',1),('b',2)])
 > isSubmapOfBy (==) (fromList [('a',1),('b',2)]) (fromList [('a',1),('b',2)])

 But the following are all 'False':

 > isSubmapOfBy (==) (fromList [('a',2)]) (fromList [('a',1),('b',2)])
 > isSubmapOfBy (<)  (fromList [('a',1)]) (fromList [('a',1),('b',2)])
 > isSubmapOfBy (==) (fromList [('a',1),('b',2)]) (fromList [('a',1)])


-}

{-@ isSubmapOfBy :: (Ord k) => (a->b->Bool) -> OMap k a -> OMap k b -> Bool @-}
isSubmapOfBy :: Ord k => (a->b->Bool) -> Map k a -> Map k b -> Bool
isSubmapOfBy f t1 t2
  = (size t1 <= size t2) && (submap' f t1 t2)
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE isSubmapOfBy #-}
#endif

submap' :: Ord a => (b -> c -> Bool) -> Map a b -> Map a c -> Bool
submap' _ Tip _ = True
submap' _ _ Tip = False
submap' f (Bin _ kx x l r) t
  = case found of
      Nothing -> False
      Just y  -> f x y && submap' f l lt && submap' f r gt
  where
    (lt,found,gt) = splitLookup kx t
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE submap' #-}
#endif

-- | /O(n+m)/. Is this a proper submap? (ie. a submap but not equal).
-- Defined as (@'isProperSubmapOf' = 'isProperSubmapOfBy' (==)@).

{-@ isProperSubmapOf :: (Ord k,Eq a) => OMap k a -> OMap k a -> Bool @-}
isProperSubmapOf :: (Ord k,Eq a) => Map k a -> Map k a -> Bool
isProperSubmapOf m1 m2
  = isProperSubmapOfBy (==) m1 m2
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE isProperSubmapOf #-}
#endif

{- | /O(n+m)/. Is this a proper submap? (ie. a submap but not equal).
 The expression (@'isProperSubmapOfBy' f m1 m2@) returns 'True' when
 @m1@ and @m2@ are not equal,
 all keys in @m1@ are in @m2@, and when @f@ returns 'True' when
 applied to their respective values. For example, the following
 expressions are all 'True':

  > isProperSubmapOfBy (==) (fromList [(1,1)]) (fromList [(1,1),(2,2)])
  > isProperSubmapOfBy (<=) (fromList [(1,1)]) (fromList [(1,1),(2,2)])

 But the following are all 'False':

  > isProperSubmapOfBy (==) (fromList [(1,1),(2,2)]) (fromList [(1,1),(2,2)])
  > isProperSubmapOfBy (==) (fromList [(1,1),(2,2)]) (fromList [(1,1)])
  > isProperSubmapOfBy (<)  (fromList [(1,1)])       (fromList [(1,1),(2,2)])


-}
{-@ isProperSubmapOfBy :: Ord k => (a -> b -> Bool) -> OMap k a -> OMap k b -> Bool @-}
isProperSubmapOfBy :: Ord k => (a -> b -> Bool) -> Map k a -> Map k b -> Bool
isProperSubmapOfBy f t1 t2
  = (size t1 < size t2) && (submap' f t1 t2)
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE isProperSubmapOfBy #-}
#endif

{--------------------------------------------------------------------
  Filter and partition
--------------------------------------------------------------------}
-- | /O(n)/. Filter all values that satisfy the predicate.
--
-- > filter (> "a") (fromList [(5,"a"), (3,"b")]) == singleton 3 "b"
-- > filter (> "x") (fromList [(5,"a"), (3,"b")]) == empty
-- > filter (< "a") (fromList [(5,"a"), (3,"b")]) == empty

{-@  filter :: (a -> Bool) -> OMap k a -> OMap k a @-}
filter :: (a -> Bool) -> Map k a -> Map k a
filter p m
  = filterWithKey (\_ x -> p x) m

-- | /O(n)/. Filter all keys\/values that satisfy the predicate.
--
-- > filterWithKey (\k _ -> k > 4) (fromList [(5,"a"), (3,"b")]) == singleton 5 "a"

{-@ filterWithKey :: (k -> a -> Bool) -> OMap k a -> OMap k a @-}
filterWithKey :: (k -> a -> Bool) -> Map k a -> Map k a
filterWithKey _ Tip = Tip
filterWithKey p (Bin _ kx x l r)
  | p kx x    = join kx x (filterWithKey p l) (filterWithKey p r)
  | otherwise = merge kx (filterWithKey p l) (filterWithKey p r)

-- | /O(n)/. Partition the map according to a predicate. The first
-- map contains all elements that satisfy the predicate, the second all
-- elements that fail the predicate. See also 'split'.
--
-- > partition (> "a") (fromList [(5,"a"), (3,"b")]) == (singleton 3 "b", singleton 5 "a")
-- > partition (< "x") (fromList [(5,"a"), (3,"b")]) == (fromList [(3, "b"), (5, "a")], empty)
-- > partition (> "x") (fromList [(5,"a"), (3,"b")]) == (empty, fromList [(3, "b"), (5, "a")])

{-@ partition :: (a -> Bool) -> OMap k a -> (OMap k a, OMap k a) @-}
partition :: (a -> Bool) -> Map k a -> (Map k a,Map k a)
partition p m
  = partitionWithKey (\_ x -> p x) m

-- | /O(n)/. Partition the map according to a predicate. The first
-- map contains all elements that satisfy the predicate, the second all
-- elements that fail the predicate. See also 'split'.
--
-- > partitionWithKey (\ k _ -> k > 3) (fromList [(5,"a"), (3,"b")]) == (singleton 5 "a", singleton 3 "b")
-- > partitionWithKey (\ k _ -> k < 7) (fromList [(5,"a"), (3,"b")]) == (fromList [(3, "b"), (5, "a")], empty)
-- > partitionWithKey (\ k _ -> k > 7) (fromList [(5,"a"), (3,"b")]) == (empty, fromList [(3, "b"), (5, "a")])

{-@ partitionWithKey :: (k -> a -> Bool) -> OMap k a -> (OMap k a, OMap k a) @-}
partitionWithKey :: (k -> a -> Bool) -> Map k a -> (Map k a, Map k a)
partitionWithKey _ Tip = (Tip,Tip)
partitionWithKey p (Bin _ kx x l r)
  | p kx x    = (join kx x l1 r1,merge kx l2 r2)
  | otherwise = (merge kx l1 r1,join kx x l2 r2)
  where
    (l1,l2) = partitionWithKey p l
    (r1,r2) = partitionWithKey p r

-- | /O(n)/. Map values and collect the 'Just' results.
--
-- > let f x = if x == "a" then Just "new a" else Nothing
-- > mapMaybe f (fromList [(5,"a"), (3,"b")]) == singleton 5 "new a"

{-@ mapMaybe :: (a -> Maybe b) -> OMap k a -> OMap k b @-}
mapMaybe :: (a -> Maybe b) -> Map k a -> Map k b
mapMaybe f = mapMaybeWithKey (\_ x -> f x)

-- | /O(n)/. Map keys\/values and collect the 'Just' results.
--
-- > let f k _ = if k < 5 then Just ("key : " ++ (show k)) else Nothing
-- > mapMaybeWithKey f (fromList [(5,"a"), (3,"b")]) == singleton 3 "key : 3"

{-@ mapMaybeWithKey :: (k -> a -> Maybe b) -> OMap k a -> OMap k b @-}
mapMaybeWithKey :: (k -> a -> Maybe b) -> Map k a -> Map k b
mapMaybeWithKey _ Tip = Tip
mapMaybeWithKey f (Bin _ kx x l r) = case f kx x of
  Just y  -> join kx y (mapMaybeWithKey f l) (mapMaybeWithKey f r)
  Nothing -> merge kx (mapMaybeWithKey f l) (mapMaybeWithKey f r)

-- | /O(n)/. Map values and separate the 'Left' and 'Right' results.
--
-- > let f a = if a < "c" then Left a else Right a
-- > mapEither f (fromList [(5,"a"), (3,"b"), (1,"x"), (7,"z")])
-- >     == (fromList [(3,"b"), (5,"a")], fromList [(1,"x"), (7,"z")])
-- >
-- > mapEither (\ a -> Right a) (fromList [(5,"a"), (3,"b"), (1,"x"), (7,"z")])
-- >     == (empty, fromList [(5,"a"), (3,"b"), (1,"x"), (7,"z")])

{-@ mapEither :: (a -> Either b c) -> OMap k a -> (OMap k b, OMap k c) @-}
mapEither :: (a -> Either b c) -> Map k a -> (Map k b, Map k c)
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

{-@ mapEitherWithKey :: (k -> a -> Either b c) -> OMap k a -> (OMap k b, OMap k c) @-}
mapEitherWithKey :: (k -> a -> Either b c) -> Map k a -> (Map k b, Map k c)
mapEitherWithKey _ Tip = (Tip, Tip)
mapEitherWithKey f (Bin _ kx x l r) = case f kx x of
  Left y  -> (join kx y l1 r1, merge kx l2 r2)
  Right z -> (merge kx l1 r1, join kx z l2 r2)
 where
    (l1,l2) = mapEitherWithKey f l
    (r1,r2) = mapEitherWithKey f r

{--------------------------------------------------------------------
  Mapping
--------------------------------------------------------------------}
-- | /O(n)/. Map a function over all values in the map.
--
-- > map (++ "x") (fromList [(5,"a"), (3,"b")]) == fromList [(3, "bx"), (5, "ax")]

{-@ map :: (a -> b) -> OMap k a -> OMap k b @-}
map :: (a -> b) -> Map k a -> Map k b
map _ Tip = Tip
map f (Bin sx kx x l r) = Bin sx kx (f x) (map f l) (map f r)

-- | /O(n)/. Map a function over all values in the map.
--
-- > let f key x = (show key) ++ ":" ++ x
-- > mapWithKey f (fromList [(5,"a"), (3,"b")]) == fromList [(3, "3:b"), (5, "5:a")]

{-@ mapWithKey :: (k -> a -> b) -> OMap k a -> OMap k b @-}
mapWithKey :: (k -> a -> b) -> Map k a -> Map k b
mapWithKey _ Tip = Tip
mapWithKey f (Bin sx kx x l r) = Bin sx kx (f kx x) (mapWithKey f l) (mapWithKey f r)

-- | /O(n)/.
-- @'traverseWithKey' f s == 'fromList' <$> 'traverse' (\(k, v) -> (,) k <$> f k v) ('toList' m)@
-- That is, behaves exactly like a regular 'traverse' except that the traversing
-- function also has access to the key associated with a value.
--
-- > traverseWithKey (\k v -> if odd k then Just (succ v) else Nothing) (fromList [(1, 'a'), (5, 'e')]) == Just (fromList [(1, 'b'), (5, 'f')])
-- > traverseWithKey (\k v -> if odd k then Just (succ v) else Nothing) (fromList [(2, 'c')])           == Nothing
--{-# INLINE traverseWithKey #-}
--traverseWithKey :: Applicative t => (k -> a -> t b) -> Map k a -> t (Map k b)
--traverseWithKey f = go
--  where
--    go Tip = pure Tip
--    go (Bin s k v l r)
--      = flip (Bin s k) <$> go l <*> f k v <*> go r

-- | /O(n)/. The function 'mapAccum' threads an accumulating
-- argument through the map in ascending order of keys.
--
-- > let f a b = (a ++ b, b ++ "X")
-- > mapAccum f "Everything: " (fromList [(5,"a"), (3,"b")]) == ("Everything: ba", fromList [(3, "bX"), (5, "aX")])

{-@ mapAccum :: (a -> b -> (a,c)) -> a -> OMap k b -> (a, OMap k c) @-}
mapAccum :: (a -> b -> (a,c)) -> a -> Map k b -> (a, Map k c)
mapAccum f a m
  = mapAccumWithKey (\a' _ x' -> f a' x') a m

-- | /O(n)/. The function 'mapAccumWithKey' threads an accumulating
-- argument through the map in ascending order of keys.
--
-- > let f a k b = (a ++ " " ++ (show k) ++ "-" ++ b, b ++ "X")
-- > mapAccumWithKey f "Everything:" (fromList [(5,"a"), (3,"b")]) == ("Everything: 3-b 5-a", fromList [(3, "bX"), (5, "aX")])

{-@ mapAccumWithKey :: (a -> k -> b -> (a,c)) -> a -> OMap k b -> (a, OMap k c) @-}
mapAccumWithKey :: (a -> k -> b -> (a,c)) -> a -> Map k b -> (a,Map k c)
mapAccumWithKey f a t
  = mapAccumL f a t

-- | /O(n)/. The function 'mapAccumL' threads an accumulating
-- argument through the map in ascending order of keys.
mapAccumL :: (a -> k -> b -> (a,c)) -> a -> Map k b -> (a,Map k c)
mapAccumL _ a Tip               = (a,Tip)
mapAccumL f a (Bin sx kx x l r) =
  let (a1,l') = mapAccumL f a l
      (a2,x') = f a1 kx x
      (a3,r') = mapAccumL f a2 r
  in (a3,Bin sx kx x' l' r')

-- | /O(n)/. The function 'mapAccumR' threads an accumulating
-- argument through the map in descending order of keys.
{-@ mapAccumRWithKey :: (a -> k -> b -> (a,c)) -> a -> OMap k b -> (a, OMap k c) @-}
mapAccumRWithKey :: (a -> k -> b -> (a,c)) -> a -> Map k b -> (a,Map k c)
mapAccumRWithKey _ a Tip = (a,Tip)
mapAccumRWithKey f a (Bin sx kx x l r) =
  let (a1,r') = mapAccumRWithKey f a r
      (a2,x') = f a1 kx x
      (a3,l') = mapAccumRWithKey f a2 l
  in (a3,Bin sx kx x' l' r')

-- | /O(n*log n)/.
-- @'mapKeys' f s@ is the map obtained by applying @f@ to each key of @s@.
--
-- The size of the result may be smaller if @f@ maps two or more distinct
-- keys to the same new key.  In this case the value at the greatest of the
-- original keys is retained.
--
-- > mapKeys (+ 1) (fromList [(5,"a"), (3,"b")])                        == fromList [(4, "b"), (6, "a")]
-- > mapKeys (\ _ -> 1) (fromList [(1,"b"), (2,"a"), (3,"d"), (4,"c")]) == singleton 1 "c"
-- > mapKeys (\ _ -> 3) (fromList [(1,"b"), (2,"a"), (3,"d"), (4,"c")]) == singleton 3 "c"

{-@ mapKeys :: (Ord k2) => (k1 -> k2) -> OMap k1 a -> OMap k2 a @-}
mapKeys :: Ord k2 => (k1->k2) -> Map k1 a -> Map k2 a
mapKeys f = fromList . foldrWithKey (\k x xs -> (f k, x) : xs) []
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE mapKeys #-}
#endif

-- | /O(n*log n)/.
-- @'mapKeysWith' c f s@ is the map obtained by applying @f@ to each key of @s@.
--
-- The size of the result may be smaller if @f@ maps two or more distinct
-- keys to the same new key.  In this case the associated values will be
-- combined using @c@.
--
-- > mapKeysWith (++) (\ _ -> 1) (fromList [(1,"b"), (2,"a"), (3,"d"), (4,"c")]) == singleton 1 "cdab"
-- > mapKeysWith (++) (\ _ -> 3) (fromList [(1,"b"), (2,"a"), (3,"d"), (4,"c")]) == singleton 3 "cdab"

{-@ mapKeysWith :: (Ord k2) => (a -> a -> a) -> (k1->k2) -> OMap k1 a -> OMap k2 a @-}
mapKeysWith :: Ord k2 => (a -> a -> a) -> (k1->k2) -> Map k1 a -> Map k2 a
mapKeysWith c f = fromListWith c . foldrWithKey (\k x xs -> (f k, x) : xs) []
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE mapKeysWith #-}
#endif


-- | /O(n)/.
-- @'mapKeysMonotonic' f s == 'mapKeys' f s@, but works only when @f@
-- is strictly monotonic.
-- That is, for any values @x@ and @y@, if @x@ < @y@ then @f x@ < @f y@.
-- /The precondition is not checked./
-- Semi-formally, we have:
--
-- > and [x < y ==> f x < f y | x <- ls, y <- ls]
-- >                     ==> mapKeysMonotonic f s == mapKeys f s
-- >     where ls = keys s
--
-- This means that @f@ maps distinct original keys to distinct resulting keys.
-- This function has better performance than 'mapKeys'.
--
-- > mapKeysMonotonic (\ k -> k * 2) (fromList [(5,"a"), (3,"b")]) == fromList [(6, "b"), (10, "a")]
-- > valid (mapKeysMonotonic (\ k -> k * 2) (fromList [(5,"a"), (3,"b")])) == True
-- > valid (mapKeysMonotonic (\ _ -> 1)     (fromList [(5,"a"), (3,"b")])) == False
-- LIQUIDFAIL
mapKeysMonotonic :: (k1->k2) -> Map k1 a -> Map k2 a
mapKeysMonotonic _ Tip = Tip
mapKeysMonotonic f (Bin sz k x l r) =
    Bin sz (f k) x (mapKeysMonotonic f l) (mapKeysMonotonic f r)

{--------------------------------------------------------------------
  Folds
--------------------------------------------------------------------}

-- | /O(n)/. Fold the values in the map using the given right-associative
-- binary operator, such that @'foldr' f z == 'Prelude.foldr' f z . 'elems'@.
--
-- For example,
--
-- > elems map = foldr (:) [] map
--
-- > let f a len = len + (length a)
-- > foldr f 0 (fromList [(5,"a"), (3,"bbb")]) == 4
foldr :: (a -> b -> b) -> b -> Map k a -> b
foldr f z = go z
  where
    go z' Tip             = z'
    go z' (Bin _ _ x l r) = go (f x (go z' r)) l
{-# INLINE foldr #-}

-- | /O(n)/. A strict version of 'foldr'. Each application of the operator is
-- evaluated before using the result in the next application. This
-- function is strict in the starting value.
foldr' :: (a -> b -> b) -> b -> Map k a -> b
foldr' f z = go z
  where
    STRICT_1_OF_2(go)
    go z' Tip             = z'
    go z' (Bin _ _ x l r) = go (f x (go z' r)) l
{-# INLINE foldr' #-}

-- | /O(n)/. Fold the values in the map using the given left-associative
-- binary operator, such that @'foldl' f z == 'Prelude.foldl' f z . 'elems'@.
--
-- For example,
--
-- > elems = reverse . foldl (flip (:)) []
--
-- > let f len a = len + (length a)
-- > foldl f 0 (fromList [(5,"a"), (3,"bbb")]) == 4
foldl :: (a -> b -> a) -> a -> Map k b -> a
foldl f z = go z
  where
    go z' Tip             = z'
    go z' (Bin _ _ x l r) = go (f (go z' l) x) r
{-# INLINE foldl #-}

-- | /O(n)/. A strict version of 'foldl'. Each application of the operator is
-- evaluated before using the result in the next application. This
-- function is strict in the starting value.
foldl' :: (a -> b -> a) -> a -> Map k b -> a
foldl' f z = go z
  where
    STRICT_1_OF_2(go)
    go z' Tip             = z'
    go z' (Bin _ _ x l r) = go (f (go z' l) x) r
{-# INLINE foldl' #-}

-- | /O(n)/. Fold the keys and values in the map using the given right-associative
-- binary operator, such that
-- @'foldrWithKey' f z == 'Prelude.foldr' ('uncurry' f) z . 'toAscList'@.
--
-- For example,
--
-- > keys map = foldrWithKey (\k x ks -> k:ks) [] map
--
-- > let f k a result = result ++ "(" ++ (show k) ++ ":" ++ a ++ ")"
-- > foldrWithKey f "Map: " (fromList [(5,"a"), (3,"b")]) == "Map: (5:a)(3:b)"
foldrWithKey :: (k -> a -> b -> b) -> b -> Map k a -> b
foldrWithKey f z = go z
  where
    go z' Tip             = z'
    go z' (Bin _ kx x l r) = go (f kx x (go z' r)) l
{-# INLINE foldrWithKey #-}

-- | /O(n)/. A strict version of 'foldrWithKey'. Each application of the operator is
-- evaluated before using the result in the next application. This
-- function is strict in the starting value.
foldrWithKey' :: (k -> a -> b -> b) -> b -> Map k a -> b
foldrWithKey' f z = go z
  where
    STRICT_1_OF_2(go)
    go z' Tip              = z'
    go z' (Bin _ kx x l r) = go (f kx x (go z' r)) l
{-# INLINE foldrWithKey' #-}

-- | /O(n)/. Fold the keys and values in the map using the given left-associative
-- binary operator, such that
-- @'foldlWithKey' f z == 'Prelude.foldl' (\\z' (kx, x) -> f z' kx x) z . 'toAscList'@.
--
-- For example,
--
-- > keys = reverse . foldlWithKey (\ks k x -> k:ks) []
--
-- > let f result k a = result ++ "(" ++ (show k) ++ ":" ++ a ++ ")"
-- > foldlWithKey f "Map: " (fromList [(5,"a"), (3,"b")]) == "Map: (3:b)(5:a)"
foldlWithKey :: (a -> k -> b -> a) -> a -> Map k b -> a
foldlWithKey f z = go z
  where
    go z' Tip              = z'
    go z' (Bin _ kx x l r) = go (f (go z' l) kx x) r
{-# INLINE foldlWithKey #-}

-- | /O(n)/. A strict version of 'foldlWithKey'. Each application of the operator is
-- evaluated before using the result in the next application. This
-- function is strict in the starting value.
foldlWithKey' :: (a -> k -> b -> a) -> a -> Map k b -> a
foldlWithKey' f z = go z
  where
    STRICT_1_OF_2(go)
    go z' Tip              = z'
    go z' (Bin _ kx x l r) = go (f (go z' l) kx x) r
{-# INLINE foldlWithKey' #-}

{--------------------------------------------------------------------
  List variations
--------------------------------------------------------------------}
-- | /O(n)/.
-- Return all elements of the map in the ascending order of their keys.
-- Subject to list fusion.
--
-- > elems (fromList [(5,"a"), (3,"b")]) == ["b","a"]
-- > elems empty == []

{-@ elems :: m:Map k a -> [a] / [mlen m] @-}
elems :: Map k a -> [a]
elems = foldr (:) []

-- | /O(n)/. Return all keys of the map in ascending order. Subject to list
-- fusion.
--
-- > keys (fromList [(5,"a"), (3,"b")]) == [3,5]
-- > keys empty == []

{- LIQUID: SUMMARY-VALUES: keys :: OMap k a -> [k]<{v: k | v >= fld}> @-}
{-@ keys :: m:Map k a -> [k] / [mlen m] @-}
keys  :: Map k a -> [k]
keys = foldrWithKey (\k _ ks -> k : ks) []

-- | /O(n)/. An alias for 'toAscList'. Return all key\/value pairs in the map
-- in ascending key order. Subject to list fusion.
--
-- > assocs (fromList [(5,"a"), (3,"b")]) == [(3,"b"), (5,"a")]
-- > assocs empty == []

{- LIQUID: SUMMARY-VALUES: assocs :: OMap k a -> [(k, a)]<{v: (k, a) | fst(v) >= fst(fld) }> @-}
assocs :: Map k a -> [(k,a)]
assocs m
  = toAscList m

-- | /O(n)/. The set of all keys of the map.
--
-- > keysSet (fromList [(5,"a"), (3,"b")]) == Data.Set.fromList [3,5]
-- > keysSet empty == Data.Set.empty
-- LIQUID keysSet :: Map k a -> Set.Set k
-- LIQUID keysSet Tip = Set.Tip
-- LIQUID keysSet (Bin sz kx _ l r) = Set.Bin sz kx (keysSet l) (keysSet r)

-- | /O(n)/. Build a map from a set of keys and a function which for each key
-- computes its value.
--
-- > fromSet (\k -> replicate k 'a') (Data.Set.fromList [3, 5]) == fromList [(5,"aaaaa"), (3,"aaa")]
-- > fromSet undefined Data.Set.empty == empty
-- LIQUID fromSet :: (k -> a) -> Set.Set k -> Map k a
-- LIQUID fromSet _ Set.Tip = Tip
-- LIQUID fromSet f (Set.Bin sz x l r) = Bin sz x (f x) (fromSet f l) (fromSet f r)

{--------------------------------------------------------------------
  Lists
  use [foldlStrict] to reduce demand on the control-stack
--------------------------------------------------------------------}
-- | /O(n*log n)/. Build a map from a list of key\/value pairs. See also 'fromAscList'.
-- If the list contains more than one value for the same key, the last value
-- for the key is retained.
--
-- > fromList [] == empty
-- > fromList [(5,"a"), (3,"b"), (5, "c")] == fromList [(5,"c"), (3,"b")]
-- > fromList [(5,"c"), (3,"b"), (5, "a")] == fromList [(5,"a"), (3,"b")]

{-@ fromList :: (Ord k) => [(k,a)] -> OMap k a @-}
fromList :: Ord k => [(k,a)] -> Map k a
fromList xs
  = foldlStrict ins empty xs
  where
    ins t (k,x) = insert k x t
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE fromList #-}
#endif

-- | /O(n*log n)/. Build a map from a list of key\/value pairs with a combining function. See also 'fromAscListWith'.
--
-- > fromListWith (++) [(5,"a"), (5,"b"), (3,"b"), (3,"a"), (5,"a")] == fromList [(3, "ab"), (5, "aba")]
-- > fromListWith (++) [] == empty

{-@ fromListWith :: (Ord k) => (a -> a -> a) -> [(k,a)] -> OMap k a @-}
fromListWith :: Ord k => (a -> a -> a) -> [(k,a)] -> Map k a
fromListWith f xs
  = fromListWithKey (\_ x y -> f x y) xs
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE fromListWith #-}
#endif

-- | /O(n*log n)/. Build a map from a list of key\/value pairs with a combining function. See also 'fromAscListWithKey'.
--
-- > let f k a1 a2 = (show k) ++ a1 ++ a2
-- > fromListWithKey f [(5,"a"), (5,"b"), (3,"b"), (3,"a"), (5,"a")] == fromList [(3, "3ab"), (5, "5a5ba")]
-- > fromListWithKey f [] == empty

{-@ fromListWithKey :: (Ord k) => (k -> a -> a -> a) -> [(k,a)] -> OMap k a @-}
fromListWithKey :: Ord k => (k -> a -> a -> a) -> [(k,a)] -> Map k a
fromListWithKey f xs
  = foldlStrict ins empty xs
  where
    ins t (k,x) = insertWithKey f k x t
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE fromListWithKey #-}
#endif

-- | /O(n)/. Convert the map to a list of key\/value pairs. Subject to list fusion.
--
-- > toList (fromList [(5,"a"), (3,"b")]) == [(3,"b"), (5,"a")]
-- > toList empty == []

{- LIQUIDTODO: toList:: OMap k a -> [(k, a)]<{v: (k, a) | fst(v) > fst(fld) }> @-}
toList :: Map k a -> [(k,a)]
toList = toAscList

-- | /O(n)/. Convert the map to a list of key\/value pairs where the keys are
-- in ascending order. Subject to list fusion.
--
-- > toAscList (fromList [(5,"a"), (3,"b")]) == [(3,"b"), (5,"a")]

{- LIQUIDTODO: toAscList :: OMap k a -> [(k, a)]<{v: (k, a) | fst(v) > fst(fld) }> @-}
{-@ toAscList :: m:Map k a -> [(k,a)] / [mlen m] @-}
toAscList :: Map k a -> [(k,a)]
toAscList = foldrWithKey (\k x xs -> (k,x):xs) []

-- | /O(n)/. Convert the map to a list of key\/value pairs where the keys
-- are in descending order. Subject to list fusion.
--
-- > toDescList (fromList [(5,"a"), (3,"b")]) == [(5,"a"), (3,"b")]

{- LIQUIDTODO: toAscList :: OMap k a -> [(k, a)]<{v: (k, a) | fst(v) < fst(fld) }> @-}
{-@ toDescList :: m:Map k a -> [(k,a)] / [mlen m] @-}
toDescList :: Map k a -> [(k,a)]
toDescList = foldlWithKey (\xs k x -> (k,x):xs) []

-- List fusion for the list generating functions.
#if __GLASGOW_HASKELL__
-- The foldrFB and foldlFB are fold{r,l}WithKey equivalents, used for list fusion.
-- They are important to convert unfused methods back, see mapFB in prelude.
{-@ foldrFB :: (k -> a -> b -> b) -> b -> m:Map k a -> b / [mlen m] @-}
foldrFB :: (k -> a -> b -> b) -> b -> Map k a -> b
foldrFB = foldrWithKey
{-# INLINE[0] foldrFB #-}
{-@ foldlFB :: (a -> k -> b -> a) -> a -> m:Map k b -> a / [mlen m] @-}
foldlFB :: (a -> k -> b -> a) -> a -> Map k b -> a
foldlFB = foldlWithKey
{-# INLINE[0] foldlFB #-}

-- Inline assocs and toList, so that we need to fuse only toAscList.
{-# INLINE assocs #-}
{-# INLINE toList #-}

-- The fusion is enabled up to phase 2 included. If it does not succeed,
-- convert in phase 1 the expanded elems,keys,to{Asc,Desc}List calls back to
-- elems,keys,to{Asc,Desc}List.  In phase 0, we inline fold{lr}FB (which were
-- used in a list fusion, otherwise it would go away in phase 1), and let compiler
-- do whatever it wants with elems,keys,to{Asc,Desc}List -- it was forbidden to
-- inline it before phase 0, otherwise the fusion rules would not fire at all.
{-# NOINLINE[0] elems #-}
{-# NOINLINE[0] keys #-}
{-# NOINLINE[0] toAscList #-}
{-# NOINLINE[0] toDescList #-}
{-# RULES "Map.elems" [~1] forall m . elems m = build (\c n -> foldrFB (\_ x xs -> c x xs) n m) #-}
{-# RULES "Map.elemsBack" [1] foldrFB (\_ x xs -> x : xs) [] = elems #-}
{-# RULES "Map.keys" [~1] forall m . keys m = build (\c n -> foldrFB (\k _ xs -> c k xs) n m) #-}
{-# RULES "Map.keysBack" [1] foldrFB (\k _ xs -> k : xs) [] = keys #-}
{-# RULES "Map.toAscList" [~1] forall m . toAscList m = build (\c n -> foldrFB (\k x xs -> c (k,x) xs) n m) #-}
{-# RULES "Map.toAscListBack" [1] foldrFB (\k x xs -> (k, x) : xs) [] = toAscList #-}
{-# RULES "Map.toDescList" [~1] forall m . toDescList m = build (\c n -> foldlFB (\xs k x -> c (k,x) xs) n m) #-}
{-# RULES "Map.toDescListBack" [1] foldlFB (\xs k x -> (k, x) : xs) [] = toDescList #-}
#endif

{--------------------------------------------------------------------
  Building trees from ascending/descending lists can be done in linear time.

  Note that if [xs] is ascending that:
    fromAscList xs       == fromList xs
    fromAscListWith f xs == fromListWith f xs
--------------------------------------------------------------------}
-- | /O(n)/. Build a map from an ascending list in linear time.
-- /The precondition (input list is ascending) is not checked./
--
-- > fromAscList [(3,"b"), (5,"a")]          == fromList [(3, "b"), (5, "a")]
-- > fromAscList [(3,"b"), (5,"a"), (5,"b")] == fromList [(3, "b"), (5, "b")]
-- > valid (fromAscList [(3,"b"), (5,"a"), (5,"b")]) == True
-- > valid (fromAscList [(5,"a"), (3,"b"), (5,"b")]) == False

{- LIQUIDTODO fromAscList :: (Eq k) => [(k,a)]<{v: (k, a) | fst(v) > fst(fld)}> -> OMap k a -}
{-@ fromAscList :: (Eq k) => {v: [(k,a)] | false} -> OMap k a @-}
fromAscList :: Eq k => [(k,a)] -> Map k a
fromAscList xs
  = fromAscListWithKey (\_ x _ -> x) xs
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE fromAscList #-}
#endif

-- | /O(n)/. Build a map from an ascending list in linear time with a combining function for equal keys.
-- /The precondition (input list is ascending) is not checked./
--
-- > fromAscListWith (++) [(3,"b"), (5,"a"), (5,"b")] == fromList [(3, "b"), (5, "ba")]
-- > valid (fromAscListWith (++) [(3,"b"), (5,"a"), (5,"b")]) == True
-- > valid (fromAscListWith (++) [(5,"a"), (3,"b"), (5,"b")]) == False

{- LIQUIDTODO fromAscListWith :: (Eq k) => (a -> a -> a) -> [(k,a)]<{v: (k, a) | fst(v) > fst(fld)}> -> OMap k a -}
{-@ fromAscListWith :: Eq k => (a -> a -> a) -> {v:[(k,a)] | false} -> OMap k a @-}
fromAscListWith :: Eq k => (a -> a -> a) -> [(k,a)] -> Map k a
fromAscListWith f xs
  = fromAscListWithKey (\_ x y -> f x y) xs
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE fromAscListWith #-}
#endif

-- | /O(n)/. Build a map from an ascending list in linear time with a
-- combining function for equal keys.
-- /The precondition (input list is ascending) is not checked./
--
-- > let f k a1 a2 = (show k) ++ ":" ++ a1 ++ a2
-- > fromAscListWithKey f [(3,"b"), (5,"a"), (5,"b"), (5,"b")] == fromList [(3, "b"), (5, "5:b5:ba")]
-- > valid (fromAscListWithKey f [(3,"b"), (5,"a"), (5,"b"), (5,"b")]) == True
-- > valid (fromAscListWithKey f [(5,"a"), (3,"b"), (5,"b"), (5,"b")]) == False

{- LIQUIDTODO fromAscListWithKey :: (Eq k) => (k -> a -> a -> a) -> [(k,a)]<{v: (k, a) | fst(v) > fst(fld)}> -> OMap k a -}
{-@ fromAscListWithKey :: (Eq k) => (k -> a -> a -> a) -> {v: [(k,a)] | false} -> OMap k a @-}
fromAscListWithKey :: Eq k => (k -> a -> a -> a) -> [(k,a)] -> Map k a
fromAscListWithKey f xs
  = fromDistinctAscList (combineEq f xs)
  where
  -- [combineEq f xs] combines equal elements with function [f] in an ordered list [xs]
  combineEq _ xs'
    = case xs' of
        []     -> []
        [x]    -> [x]
        (x:xx) -> combineEq' x xx

  combineEq' z [] = [z]
  combineEq' z@(kz,zz) (x@(kx,xx):xs')
    | kx==kz    = let yy = f kx xx zz in combineEq' (kx,yy) xs'
    | otherwise = z:combineEq' x xs'
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE fromAscListWithKey #-}
#endif


-- | /O(n)/. Build a map from an ascending list of distinct elements in linear time.
-- /The precondition is not checked./
--
-- > fromDistinctAscList [(3,"b"), (5,"a")] == fromList [(3, "b"), (5, "a")]
-- > valid (fromDistinctAscList [(3,"b"), (5,"a")])          == True
-- > valid (fromDistinctAscList [(3,"b"), (5,"a"), (5,"b")]) == False

{- LIQUIDTODO fromDistinctAscList :: [(k,a)]<{v: (k, a) | fst(v) > fst(fld)}> -> OMap k a -}
{-@ Lazy fromDistinctAscList @-}
{-@ fromDistinctAscList :: {v: [(k, a)] | false} -> OMap k a @-}
fromDistinctAscList :: [(k,a)] -> Map k a
fromDistinctAscList xs
  = create const (length xs) xs
  where
    -- 1) use continuations so that we use heap space instead of stack space.
    -- 2) special case for n==5 to create bushier trees.
    create c 0 xs' = c Tip xs'
    create c 5 xs' = case xs' of
                       ((k1,x1):(k2,x2):(k3,x3):(k4,x4):(k5,x5):xx)
                            -> c (bin k4 x4 (bin k2 x2 (singleton k1 x1) (singleton k3 x3)) (singleton k5 x5)) xx
                       _ -> error "fromDistinctAscList create"
    create c n xs' = seq nr $ create (createR nr c) nl xs'
      where nl = n `div` 2
            nr = n - nl - 1

    createR n c l ((k,x):ys) = create (createB l k x c) n ys
    createR _ _ _ []         = error "fromDistinctAscList createR []"
    createB l k x c r zs     = c (bin k x l r) zs


{--------------------------------------------------------------------
  Utility functions that return sub-ranges of the original
  tree. Some functions take a `Maybe value` as an argument to
  allow comparisons against infinite values. These are called `blow`
  (Nothing is -\infty) and `bhigh` (here Nothing is +\infty).
  We use MaybeS value, which is a Maybe strict in the Just case.

  [trim blow bhigh t]   A tree that is either empty or where [x > blow]
                        and [x < bhigh] for the value [x] of the root.
  [filterGt blow t]     A tree where for all values [k]. [k > blow]
  [filterLt bhigh t]    A tree where for all values [k]. [k < bhigh]

  [split k t]           Returns two trees [l] and [r] where all keys
                        in [l] are <[k] and all keys in [r] are >[k].
  [splitLookup k t]     Just like [split] but also returns whether [k]
                        was found in the tree.
--------------------------------------------------------------------}

data MaybeS a = NothingS | JustS a -- LIQUID: !-annot-fix


{--------------------------------------------------------------------
  [trim blo bhi t] trims away all subtrees that surely contain no
  values between the range [blo] to [bhi]. The returned tree is either
  empty or the key of the root is between @blo@ and @bhi@.
--------------------------------------------------------------------}
-- LIQUID: EXPANDED CASE-EXPRS for lesser, greater, middle to avoid DEFAULT hassle
{-@ trim :: (Ord k) => lo:MaybeS k 
                    -> hi:MaybeS k 
                    -> OMap k a 
                    -> {v: OMap k a | (RootBetween lo hi v) }                       
                    @-}
                    

trim :: Ord k => MaybeS k -> MaybeS k -> Map k a -> Map k a


trim NothingS   NothingS   t = t
trim (JustS lk) NothingS   t = greater lk t 

  where greater lo t@(Bin _ k _ _ r) | k <= lo      = greater lo r
                                     | otherwise    = t
        greater _  t'@Tip                           = t'

trim NothingS   (JustS hk) t = lesser hk t 

  where lesser  hi t'@(Bin _ k _ l _) | k >= hi     = lesser  hi l
                                      | otherwise   = t'
        lesser  _  t'@Tip                           = t'
trim (JustS lk) (JustS hk) t = middle lk hk t  
  where middle lo hi t'@(Bin _ k _ l r) | k <= lo   = middle lo hi r
                                        | k >= hi   = middle lo hi l
                                        | otherwise = t'
        middle _ _ t'@Tip = t'  
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE trim #-}
#endif

-- LIQUID QUALIFIER DEBUG SILLINESS
{-@ zoo1 :: (Ord k) => lo:k -> OMap k a -> {v: OMap k a | ((isBin(v)) => (lo < key(v)))} @-}
zoo1 :: Ord k => k -> Map k a -> Map k a
zoo1 = error "TODO"

{-@ zoo2 :: (Ord k) => lo:k -> OMap k a -> {v: OMap k a | ((isBin(v)) => (lo > key(v)))} @-}
zoo2 :: Ord k => k -> Map k a -> Map k a
zoo2 = error "TODO"


-- Helper function for 'mergeWithKey'. The @'trimLookupLo' lk hk t@ performs both
-- @'trim' (JustS lk) hk t@ and @'lookup' lk t@.

-- See Note: Type of local 'go' function
-- LIQUID trimLookupLo :: Ord k => k -> MaybeS k -> Map k a -> (Maybe a, Map k a)
-- LIQUID trimLookupLo lk NothingS t = greater lk t
-- LIQUID   where greater :: Ord k => k -> Map k a -> (Maybe a, Map k a)
-- LIQUID         greater lo t'@(Bin _ kx x l r) = case compare lo kx of LT -> (lookup lo l, {-`strictPair`-} t')
-- LIQUID                                                                EQ -> (Just x, r)
-- LIQUID                                                                GT -> greater lo r
-- LIQUID         greater _ Tip = (Nothing, Tip)
-- LIQUID trimLookupLo lk (JustS hk) t = middle lk hk t
-- LIQUID   where middle :: Ord k => k -> k -> Map k a -> (Maybe a, Map k a)
-- LIQUID         middle lo hi t'@(Bin _ kx x l r) = case compare lo kx of LT | kx < hi -> (lookup lo l, {- `strictPair` -} t')
-- LIQUID                                                                     | otherwise -> middle lo hi l
-- LIQUID                                                                  EQ -> (Just x, {-`strictPair`-} lesser hi r)
-- LIQUID                                                                  GT -> middle lo hi r
-- LIQUID         middle _ _ Tip = (Nothing, Tip)
-- LIQUID 
-- LIQUID         lesser :: Ord k => k -> Map k a -> Map k a
-- LIQUID         lesser hi (Bin _ k _ l _) | k >= hi = lesser hi l
-- LIQUID         lesser _ t' = t'

{-@ trimLookupLo :: (Ord k) 
                 => lo:k 
                 -> bhi:{v: MaybeS k | (isJustS(v) => (lo < fromJustS(v)))} 
                 -> OMap k a 
                 -> (Maybe a, {v: OMap k a | ((isBin(v) => (lo < key(v))) && ((isBin(v) && isJustS(bhi)) => (fromJustS(bhi) > key(v)))) }) @-}

trimLookupLo :: Ord k => k -> MaybeS k -> Map k a -> (Maybe a, Map k a)
trimLookupLo lk NothingS t = greater lk t
  where greater :: Ord k => k -> Map k a -> (Maybe a, Map k a)
        greater lo t'@(Bin _ kx x l r) = case compare lo kx of LT -> (lookup lo l, {-`strictPair`-} t')
                                                               EQ -> (Just x, (case r of {r'@(Bin _ _ _ _ _) -> r' ; r'@Tip -> r'}))
                                                               GT -> greater lo r
        greater _ Tip = (Nothing, Tip)
trimLookupLo lk (JustS hk) t = middle lk hk t
  where middle :: Ord k => k -> k -> Map k a -> (Maybe a, Map k a)
        middle lo hi t'@(Bin _ kx x l r) = case compare lo kx of LT | kx < hi -> (lookup lo l, {- `strictPair` -} t')
                                                                    | otherwise -> middle lo hi l
                                                                 EQ -> (Just x, {-`strictPair`-} lesser lo hi (case r of {r'@(Bin _ _ _ _ _) -> r' ; r'@Tip -> r'}))
                                                                 GT -> middle lo hi r
        middle _ _ Tip = (Nothing, Tip)
 
        lesser :: Ord k => k -> k -> Map k a -> Map k a
        lesser lo hi t'@(Bin _ k _ l _) | k >= hi   = lesser lo hi l
                                        | otherwise = t'
        lesser _ _ t'@Tip = t'
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE trimLookupLo #-}
#endif


{--------------------------------------------------------------------
  [filterGt b t] filter all keys >[b] from tree [t]
  [filterLt b t] filter all keys <[b] from tree [t]
--------------------------------------------------------------------}

{-@ filterGt :: (Ord k) => x:MaybeS k -> OMap k v -> OMap {v:k | ((isJustS(x)) => (v > fromJustS(x))) } v @-}
filterGt :: Ord k => MaybeS k -> Map k v -> Map k v
filterGt NothingS t = t
filterGt (JustS b) t = filterGt' b t

-- LIQUID TXREC-TOPLEVEL-ISSUE
filterGt' _   Tip = Tip
filterGt' b' (Bin _ kx x l r) =
          case compare b' kx of LT -> join kx x (filterGt' b' l) r
                                EQ -> r
                                GT -> filterGt' b' r
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE filterGt #-}
#endif

{-@ filterLt :: (Ord k) => x:MaybeS k -> OMap k v -> OMap {v:k | ((isJustS(x)) => (v < fromJustS(x))) } v @-}
filterLt :: Ord k => MaybeS k -> Map k v -> Map k v
filterLt NothingS t = t
filterLt (JustS b) t = filterLt' b t

-- LIQUID TXREC-TOPLEVEL-ISSUE
filterLt' _   Tip = Tip
filterLt' b' (Bin _ kx x l r) =
          case compare kx b' of LT -> join kx x l (filterLt' b' r)
                                EQ -> l
                                GT -> filterLt' b' l
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE filterLt #-}
#endif

{--------------------------------------------------------------------
  Split
--------------------------------------------------------------------}
-- | /O(log n)/. The expression (@'split' k map@) is a pair @(map1,map2)@ where
-- the keys in @map1@ are smaller than @k@ and the keys in @map2@ larger than @k@.
-- Any key equal to @k@ is found in neither @map1@ nor @map2@.
--
-- > split 2 (fromList [(5,"a"), (3,"b")]) == (empty, fromList [(3,"b"), (5,"a")])
-- > split 3 (fromList [(5,"a"), (3,"b")]) == (empty, singleton 5 "a")
-- > split 4 (fromList [(5,"a"), (3,"b")]) == (singleton 3 "b", singleton 5 "a")
-- > split 5 (fromList [(5,"a"), (3,"b")]) == (singleton 3 "b", empty)
-- > split 6 (fromList [(5,"a"), (3,"b")]) == (fromList [(3,"b"), (5,"a")], empty)

{-@ split :: (Ord k) => x:k -> OMap k a -> (OMap {v: k | v < x} a, OMap {v:k | v > x} a) @-}
split :: Ord k => k -> Map k a -> (Map k a, Map k a)
split k t = k `seq`
  case t of
    Tip            -> (Tip, Tip)
    Bin _ kx x l r -> case compare k kx of
      LT -> let (lt,gt) = split k l in (lt,join kx x gt r)
      GT -> let (lt,gt) = split k r in (join kx x l lt,gt)
      EQ -> (l,r)
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE split #-}
#endif

-- | /O(log n)/. The expression (@'splitLookup' k map@) splits a map just
-- like 'split' but also returns @'lookup' k map@.
--
-- > splitLookup 2 (fromList [(5,"a"), (3,"b")]) == (empty, Nothing, fromList [(3,"b"), (5,"a")])
-- > splitLookup 3 (fromList [(5,"a"), (3,"b")]) == (empty, Just "b", singleton 5 "a")
-- > splitLookup 4 (fromList [(5,"a"), (3,"b")]) == (singleton 3 "b", Nothing, singleton 5 "a")
-- > splitLookup 5 (fromList [(5,"a"), (3,"b")]) == (singleton 3 "b", Just "a", empty)
-- > splitLookup 6 (fromList [(5,"a"), (3,"b")]) == (fromList [(3,"b"), (5,"a")], Nothing, empty)

{-@ splitLookup :: (Ord k) => x:k -> OMap k a -> (OMap {v: k | v < x} a, Maybe a, OMap {v:k | v > x} a) @-}
splitLookup :: Ord k => k -> Map k a -> (Map k a,Maybe a,Map k a)
splitLookup k t = k `seq`
  case t of
    Tip            -> (Tip,Nothing,Tip)
    Bin _ kx x l r -> case compare k kx of
      LT -> let (lt,z,gt) = splitLookup k l in (lt,z,join kx x gt r)
      GT -> let (lt,z,gt) = splitLookup k r in (join kx x l lt,z,gt)
      EQ -> (l,Just x,r)
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE splitLookup #-}
#endif

{--------------------------------------------------------------------
  Utility functions that maintain the balance properties of the tree.
  All constructors assume that all values in [l] < [k] and all values
  in [r] > [k], and that [l] and [r] are valid trees.

  In order of sophistication:
    [Bin sz k x l r]  The type constructor.
    [bin k x l r]     Maintains the correct size, assumes that both [l]
                      and [r] are balanced with respect to each other.
    [balance k x l r] Restores the balance and size.
                      Assumes that the original tree was balanced and
                      that [l] or [r] has changed by at most one element.
    [join k x l r]    Restores balance and size.

  Furthermore, we can construct a new tree from two trees. Both operations
  assume that all values in [l] < all values in [r] and that [l] and [r]
  are valid:
    [glue l r]        Glues [l] and [r] together. Assumes that [l] and
                      [r] are already balanced with respect to each other.
    [merge l r]       Merges two trees and restores balance.

  Note: in contrast to Adam's paper, we use (<=) comparisons instead
  of (<) comparisons in [join], [merge] and [balance].
  Quickcheck (on [difference]) showed that this was necessary in order
  to maintain the invariants. It is quite unsatisfactory that I haven't
  been able to find out why this is actually the case! Fortunately, it
  doesn't hurt to be a bit more conservative.
--------------------------------------------------------------------}
{--------------------------------------------------------------------
  Join
--------------------------------------------------------------------}

{-@ join :: k:k -> a -> OMap {v:k | v < k} a -> OMap {v:k| v > k} a -> OMap k a @-}
join :: k -> a -> Map k a -> Map k a -> Map k a
join k x m1 m2 = joinT k x m1 m2 (mlen m1 + mlen m2)
--LIQUID join kx x Tip r  = insertMin kx x r
--LIQUID join kx x l Tip  = insertMax kx x l
--LIQUID join kx x l@(Bin sizeL ky y ly ry) r@(Bin sizeR kz z lz rz)
--LIQUID   | delta*sizeL < sizeR  = balanceL kz z (join kx x l lz) rz
--LIQUID   | delta*sizeR < sizeL  = balanceR ky y ly (join kx x ry r)
--LIQUID   | otherwise            = bin kx x l r

{-@ joinT :: k:k -> a -> a:OMap {v:k | v < k} a -> b:OMap {v:k| v > k} a -> SumMLen a b -> OMap k a @-}
{-@ Decrease joinT 5 @-}
{- LIQUID WITNESS -}
joinT :: k -> a -> Map k a -> Map k a -> Int -> Map k a
joinT kx x Tip r _ = insertMin kx x r
joinT kx x l Tip _ = insertMax kx x l
joinT kx x l@(Bin sizeL ky y ly ry) r@(Bin sizeR kz z lz rz) d
  | delta*sizeL < sizeR  = balanceL kz z (joinT kx x l lz (d-(mlen rz)-1)) rz
  | delta*sizeR < sizeL  = balanceR ky y ly (joinT kx x ry r (d-(mlen ly)-1))
  | otherwise            = bin kx x l r

-- insertMin and insertMax don't perform potentially expensive comparisons.
insertMax, insertMin :: k -> a -> Map k a -> Map k a
insertMax kx x t
  = case t of
      Tip -> singleton kx x
      Bin _ ky y l r
          -> balanceR ky y l (insertMax kx x r)

insertMin kx x t
  = case t of
      Tip -> singleton kx x
      Bin _ ky y l r
          -> balanceL ky y (insertMin kx x l) r

{--------------------------------------------------------------------
  [merge l r]: merges two trees.
--------------------------------------------------------------------}
{-@ merge :: kcut:k -> OMap {v:k | v < kcut} a -> OMap {v:k| v > kcut} a -> OMap k a @-}
merge :: k -> Map k a -> Map k a -> Map k a
merge k m1 m2 = mergeT k m1 m2 (mlen m1 + mlen m2)
--LIQUID merge _   Tip r   = r
--LIQUID merge _   l Tip   = l
--LIQUID merge kcut l@(Bin sizeL kx x lx rx) r@(Bin sizeR ky y ly ry)
--LIQUID   | delta*sizeL < sizeR = balanceL ky y (merge kcut l ly) ry
--LIQUID   | delta*sizeR < sizeL = balanceR kx x lx (merge kcut rx r)
--LIQUID   | otherwise           = glue kcut l r

{-@ mergeT :: kcut:k -> a:OMap {v:k | v < kcut} a -> b:OMap {v:k| v > kcut} a -> SumMLen a b -> OMap k a @-}
{-@ Decrease mergeT 4 @-}
{- LIQUID WITNESS -}
mergeT :: k -> Map k a -> Map k a -> Int -> Map k a
mergeT _   Tip r _   = r
mergeT _   l Tip _   = l
mergeT kcut l@(Bin sizeL kx x lx rx) r@(Bin sizeR ky y ly ry) d
  | delta*sizeL < sizeR = balanceL ky y (mergeT kcut l ly (d-(mlen ry)-1)) ry
  | delta*sizeR < sizeL = balanceR kx x lx (mergeT kcut rx r (d-(mlen lx)-1))
  | otherwise           = glue kcut l r

{--------------------------------------------------------------------
  [glue l r]: glues two trees together.
  Assumes that [l] and [r] are already balanced with respect to each other.
--------------------------------------------------------------------}
{-@ glue :: kcut:k -> OMap {v:k | v < kcut} a -> OMap {v:k| v > kcut} a -> OMap k a @-}
glue :: k -> Map k a -> Map k a -> Map k a
glue _    Tip r = r
glue _    l Tip = l
glue kcut l r
  | size l > size r = let (km, m, l') = deleteFindMax l in balanceR km m l' r
  | otherwise       = let (km, m, r') = deleteFindMin r in balanceL km m l r'

-- | /O(log n)/. Delete and find the minimal element.
--
-- > deleteFindMin (fromList [(5,"a"), (3,"b"), (10,"c")]) == ((3,"b"), fromList[(5,"a"), (10,"c")])
-- > deleteFindMin                                            Error: can not return the minimal element of an empty map

{-@ deleteFindMin :: OMap k a -> (k, a, OMap k a)<{\k a -> true}, \a k -> {v0:Map ({v:k | v > k}) a | true}> @-}
deleteFindMin :: Map k a -> (k, a, Map k a)
deleteFindMin t
  = case t of
      Bin _ k x Tip r -> (k, x, r)
      Bin _ k x l r   -> let (km, m, l') = deleteFindMin l in (km, m, balanceR k x l' r)
      Tip             -> error "Map.deleteFindMin: can not return the minimal element of an empty map"

-- | /O(log n)/. Delete and find the maximal element.
--
-- > deleteFindMax (fromList [(5,"a"), (3,"b"), (10,"c")]) == ((10,"c"), fromList [(3,"b"), (5,"a")])
-- > deleteFindMax empty                                      Error: can not return the maximal element of an empty map

{-@ deleteFindMax :: OMap k a -> (k, a, OMap k a)<{\k a -> true}, \a k -> {v0:Map ({v:k | v < k}) a | true}> @-}
deleteFindMax :: Map k a -> (k, a, Map k a)
deleteFindMax t
  = case t of
      Bin _ k x l Tip -> (k, x, l)
      Bin _ k x l r   -> let (km, m, r') = deleteFindMax r in (km, m, balanceL k x l r')
      Tip             -> error "Map.deleteFindMax: can not return the maximal element of an empty map"


{--------------------------------------------------------------------
  [balance l x r] balances two trees with value x.
  The sizes of the trees should balance after decreasing the
  size of one of them. (a rotation).

  [delta] is the maximal relative difference between the sizes of
          two trees, it corresponds with the [w] in Adams' paper.
  [ratio] is the ratio between an outer and inner sibling of the
          heavier subtree in an unbalanced setting. It determines
          whether a double or single rotation should be performed
          to restore balance. It is corresponds with the inverse
          of $\alpha$ in Adam's article.

  Note that according to the Adam's paper:
  - [delta] should be larger than 4.646 with a [ratio] of 2.
  - [delta] should be larger than 3.745 with a [ratio] of 1.534.

  But the Adam's paper is erroneous:
  - It can be proved that for delta=2 and delta>=5 there does
    not exist any ratio that would work.
  - Delta=4.5 and ratio=2 does not work.

  That leaves two reasonable variants, delta=3 and delta=4,
  both with ratio=2.

  - A lower [delta] leads to a more 'perfectly' balanced tree.
  - A higher [delta] performs less rebalancing.

  In the benchmarks, delta=3 is faster on insert operations,
  and delta=4 has slightly better deletes. As the insert speedup
  is larger, we currently use delta=3.

--------------------------------------------------------------------}
delta,ratio :: Int
delta = 3
ratio = 2

-- The balance function is equivalent to the following:
--
--   balance :: k -> a -> Map k a -> Map k a -> Map k a
--   balance k x l r
--     | sizeL + sizeR <= 1    = Bin sizeX k x l r
--     | sizeR > delta*sizeL   = rotateL k x l r
--     | sizeL > delta*sizeR   = rotateR k x l r
--     | otherwise             = Bin sizeX k x l r
--     where
--       sizeL = size l
--       sizeR = size r
--       sizeX = sizeL + sizeR + 1
--
--   rotateL :: a -> b -> Map a b -> Map a b -> Map a b
--   rotateL k x l r@(Bin _ _ _ ly ry) | size ly < ratio*size ry = singleL k x l r
--                                     | otherwise               = doubleL k x l r
--
--   rotateR :: a -> b -> Map a b -> Map a b -> Map a b
--   rotateR k x l@(Bin _ _ _ ly ry) r | size ry < ratio*size ly = singleR k x l r
--                                     | otherwise               = doubleR k x l r
--
--   singleL, singleR :: a -> b -> Map a b -> Map a b -> Map a b
--   singleL k1 x1 t1 (Bin _ k2 x2 t2 t3)  = bin k2 x2 (bin k1 x1 t1 t2) t3
--   singleR k1 x1 (Bin _ k2 x2 t1 t2) t3  = bin k2 x2 t1 (bin k1 x1 t2 t3)
--
--   doubleL, doubleR :: a -> b -> Map a b -> Map a b -> Map a b
--   doubleL k1 x1 t1 (Bin _ k2 x2 (Bin _ k3 x3 t2 t3) t4) = bin k3 x3 (bin k1 x1 t1 t2) (bin k2 x2 t3 t4)
--   doubleR k1 x1 (Bin _ k2 x2 t1 (Bin _ k3 x3 t2 t3)) t4 = bin k3 x3 (bin k2 x2 t1 t2) (bin k1 x1 t3 t4)
--
-- It is only written in such a way that every node is pattern-matched only once.

{-@ balance :: k:k -> a -> OMap {v:k|v<k} a -> OMap {v:k|v>k} a -> OMap k a @-}
balance :: k -> a -> Map k a -> Map k a -> Map k a
balance k x l r = case l of
  Tip -> case r of
           Tip -> Bin 1 k x Tip Tip
           (Bin _ _ _ Tip Tip) -> Bin 2 k x Tip r
           (Bin _ rk rx Tip rr@(Bin _ _ _ _ _)) -> Bin 3 rk rx (Bin 1 k x Tip Tip) rr
           (Bin _ rk rx (Bin _ rlk rlx _ _) Tip) -> Bin 3 rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)
           (Bin rs rk rx rl@(Bin rls rlk rlx rll rlr) rr@(Bin rrs _ _ _ _))
             | rls < ratio*rrs -> Bin (1+rs) rk rx (Bin (1+rls) k x Tip rl) rr
             | otherwise -> Bin (1+rs) rlk rlx (Bin (1+size rll) k x Tip rll) (Bin (1+rrs+size rlr) rk rx rlr rr)

  (Bin ls lk lx ll lr) -> case r of
           Tip -> case (ll, lr) of
                    (Tip, Tip) -> Bin 2 k x l Tip
                    (Tip, (Bin _ lrk lrx _ _)) -> Bin 3 lrk lrx (Bin 1 lk lx Tip Tip) (Bin 1 k x Tip Tip)
                    ((Bin _ _ _ _ _), Tip) -> Bin 3 lk lx ll (Bin 1 k x Tip Tip)
                    ((Bin lls _ _ _ _), (Bin lrs lrk lrx lrl lrr))
                      | lrs < ratio*lls -> Bin (1+ls) lk lx ll (Bin (1+lrs) k x lr Tip)
                      | otherwise -> Bin (1+ls) lrk lrx (Bin (1+lls+size lrl) lk lx ll lrl) (Bin (1+size lrr) k x lrr Tip)
           (Bin rs rk rx rl rr)
              | rs > delta*ls  -> case (rl, rr) of
                   (Bin rls rlk rlx rll rlr, Bin rrs _ _ _ _)
                     | rls < ratio*rrs -> Bin (1+ls+rs) rk rx (Bin (1+ls+rls) k x l rl) rr
                     | otherwise -> Bin (1+ls+rs) rlk rlx (Bin (1+ls+size rll) k x l rll) (Bin (1+rrs+size rlr) rk rx rlr rr)
                   (_, _) -> error "Failure in Data.Map.balance"
              | ls > delta*rs  -> case (ll, lr) of
                   (Bin lls _ _ _ _, Bin lrs lrk lrx lrl lrr)
                     | lrs < ratio*lls -> Bin (1+ls+rs) lk lx ll (Bin (1+rs+lrs) k x lr r)
                     | otherwise -> Bin (1+ls+rs) lrk lrx (Bin (1+lls+size lrl) lk lx ll lrl) (Bin (1+rs+size lrr) k x lrr r)
                   (_, _) -> error "Failure in Data.Map.balance"
              | otherwise -> Bin (1+ls+rs) k x l r
{-# NOINLINE balance #-}

-- Functions balanceL and balanceR are specialised versions of balance.
-- balanceL only checks whether the left subtree is too big,
-- balanceR only checks whether the right subtree is too big.

-- balanceL is called when left subtree might have been inserted to or when
-- right subtree might have been deleted from.
{-@ balanceL :: kcut:k -> a -> OMap {v:k | v < kcut} a -> OMap {v:k| v > kcut} a -> OMap k a @-}
balanceL :: k -> a -> Map k a -> Map k a -> Map k a
balanceL k x l r = case r of
  Tip -> case l of
           Tip -> Bin 1 k x Tip Tip
           (Bin _ _ _ Tip Tip) -> Bin 2 k x l Tip
           (Bin _ lk lx Tip (Bin _ lrk lrx _ _)) -> Bin 3 lrk lrx (Bin 1 lk lx Tip Tip) (Bin 1 k x Tip Tip)
           (Bin _ lk lx ll@(Bin _ _ _ _ _) Tip) -> Bin 3 lk lx ll (Bin 1 k x Tip Tip)
           (Bin ls lk lx ll@(Bin lls _ _ _ _) lr@(Bin lrs lrk lrx lrl lrr))
             | lrs < ratio*lls -> Bin (1+ls) lk lx ll (Bin (1+lrs) k x lr Tip)
             | otherwise -> Bin (1+ls) lrk lrx (Bin (1+lls+size lrl) lk lx ll lrl) (Bin (1+size lrr) k x lrr Tip)

  (Bin rs _ _ _ _) -> case l of
           Tip -> Bin (1+rs) k x Tip r

           (Bin ls lk lx ll lr)
              | ls > delta*rs  -> case (ll, lr) of
                   (Bin lls _ _ _ _, Bin lrs lrk lrx lrl lrr)
                     | lrs < ratio*lls -> Bin (1+ls+rs) lk lx ll (Bin (1+rs+lrs) k x lr r)
                     | otherwise -> Bin (1+ls+rs) lrk lrx (Bin (1+lls+size lrl) lk lx ll lrl) (Bin (1+rs+size lrr) k x lrr r)
                   (_, _) -> error "Failure in Data.Map.balanceL"
              | otherwise -> Bin (1+ls+rs) k x l r
{-# NOINLINE balanceL #-}

-- balanceR is called when right subtree might have been inserted to or when
-- left subtree might have been deleted from.
{-@ balanceR :: kcut:k -> a -> OMap {v:k | v < kcut} a -> OMap {v:k| v > kcut} a -> OMap k a @-}
balanceR :: k -> a -> Map k a -> Map k a -> Map k a
balanceR k x l r = case l of
  Tip -> case r of
           Tip -> Bin 1 k x Tip Tip
           (Bin _ _ _ Tip Tip) -> Bin 2 k x Tip r
           (Bin _ rk rx Tip rr@(Bin _ _ _ _ _)) -> Bin 3 rk rx (Bin 1 k x Tip Tip) rr
           (Bin _ rk rx (Bin _ rlk rlx _ _) Tip) -> Bin 3 rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)
           (Bin rs rk rx rl@(Bin rls rlk rlx rll rlr) rr@(Bin rrs _ _ _ _))
             | rls < ratio*rrs -> Bin (1+rs) rk rx (Bin (1+rls) k x Tip rl) rr
             | otherwise -> Bin (1+rs) rlk rlx (Bin (1+size rll) k x Tip rll) (Bin (1+rrs+size rlr) rk rx rlr rr)

  (Bin ls _ _ _ _) -> case r of
           Tip -> Bin (1+ls) k x l Tip

           (Bin rs rk rx rl rr)
              | rs > delta*ls  -> case (rl, rr) of
                   (Bin rls rlk rlx rll rlr, Bin rrs _ _ _ _)
                     | rls < ratio*rrs -> Bin (1+ls+rs) rk rx (Bin (1+ls+rls) k x l rl) rr
                     | otherwise -> Bin (1+ls+rs) rlk rlx (Bin (1+ls+size rll) k x l rll) (Bin (1+rrs+size rlr) rk rx rlr rr)
                   (_, _) -> error "Failure in Data.Map.balanceR"
              | otherwise -> Bin (1+ls+rs) k x l r
{-# NOINLINE balanceR #-}


{--------------------------------------------------------------------
  The bin constructor maintains the size of the tree
--------------------------------------------------------------------}
{-@ bin :: k:k -> a -> OMap {v:k | v < k} a -> OMap {v:k| v > k} a -> OMap k a @-}
bin :: k -> a -> Map k a -> Map k a -> Map k a
bin k x l r
  = Bin (size l + size r + 1) k x l r
{-# INLINE bin #-}

{--------------------------------------------------------------------
  Eq converts the tree to a list. In a lazy setting, this
  actually seems one of the faster methods to compare two trees
  and it is certainly the simplest :-)
--------------------------------------------------------------------}
instance (Eq k,Eq a) => Eq (Map k a) where
  t1 == t2  = (size t1 == size t2) && (toAscList t1 == toAscList t2)

{--------------------------------------------------------------------
  Ord
--------------------------------------------------------------------}

instance (Ord k, Ord v) => Ord (Map k v) where
    compare m1 m2 = compare (toAscList m1) (toAscList m2)

{--------------------------------------------------------------------
  Functor
--------------------------------------------------------------------}

-- LIQUID instance Functor (Map k) where
-- LIQUID   fmap f m  = map f m
-- LIQUID 
-- LIQUID instance Traversable (Map k) where
-- LIQUID   traverse f = traverseWithKey (\_ -> f)
-- LIQUID 
-- LIQUID instance Foldable.Foldable (Map k) where
-- LIQUID   fold Tip = mempty
-- LIQUID   fold (Bin _ _ v l r) = Foldable.fold l `mappend` v `mappend` Foldable.fold r
-- LIQUID   foldr = foldr
-- LIQUID   foldl = foldl
-- LIQUID   foldMap _ Tip = mempty
-- LIQUID   foldMap f (Bin _ _ v l r) = Foldable.foldMap f l `mappend` f v `mappend` Foldable.foldMap f r
-- LIQUID 
-- LIQUID instance (NFData k, NFData a) => NFData (Map k a) where
-- LIQUID     rnf Tip = ()
-- LIQUID     rnf (Bin _ kx x l r) = rnf kx `seq` rnf x `seq` rnf l `seq` rnf r

{--------------------------------------------------------------------
  Read
--------------------------------------------------------------------}
-- LIQUID instance (Ord k, Read k, Read e) => Read (Map k e) where
-- LIQUID #ifdef __GLASGOW_HASKELL__
-- LIQUID   readPrec = parens $ prec 10 $ do
-- LIQUID     Ident "fromList" <- lexP
-- LIQUID     xs <- readPrec
-- LIQUID     return (fromList xs)
-- LIQUID 
-- LIQUID   readListPrec = readListPrecDefault
-- LIQUID #else
-- LIQUID   readsPrec p = readParen (p > 10) $ \ r -> do
-- LIQUID     ("fromList",s) <- lex r
-- LIQUID     (xs,t) <- reads s
-- LIQUID     return (fromList xs,t)
-- LIQUID #endif

{--------------------------------------------------------------------
  Show
--------------------------------------------------------------------}
-- LIQUID instance (Show k, Show a) => Show (Map k a) where
-- LIQUID   showsPrec d m  = showParen (d > 10) $
-- LIQUID     showString "fromList " . shows (toList m)

-- | /O(n)/. Show the tree that implements the map. The tree is shown
-- in a compressed, hanging format. See 'showTreeWith'.
showTree :: (Show k,Show a) => Map k a -> String
showTree m
  = showTreeWith showElem True False m
  where
    showElem k x  = show k ++ ":=" ++ show x


{- | /O(n)/. The expression (@'showTreeWith' showelem hang wide map@) shows
 the tree that implements the map. Elements are shown using the @showElem@ function. If @hang@ is
 'True', a /hanging/ tree is shown otherwise a rotated tree is shown. If
 @wide@ is 'True', an extra wide version is shown.

>  Map> let t = fromDistinctAscList [(x,()) | x <- [1..5]]
>  Map> putStrLn $ showTreeWith (\k x -> show (k,x)) True False t
>  (4,())
>  +--(2,())
>  |  +--(1,())
>  |  +--(3,())
>  +--(5,())
>
>  Map> putStrLn $ showTreeWith (\k x -> show (k,x)) True True t
>  (4,())
>  |
>  +--(2,())
>  |  |
>  |  +--(1,())
>  |  |
>  |  +--(3,())
>  |
>  +--(5,())
>
>  Map> putStrLn $ showTreeWith (\k x -> show (k,x)) False True t
>  +--(5,())
>  |
>  (4,())
>  |
>  |  +--(3,())
>  |  |
>  +--(2,())
>     |
>     +--(1,())

-}
showTreeWith :: (k -> a -> String) -> Bool -> Bool -> Map k a -> String
showTreeWith showelem hang wide t
  | hang      = (showsTreeHang showelem wide [] t) ""
  | otherwise = (showsTree showelem wide [] [] t) ""

{-@ Decrease showsTree 5 @-}
showsTree :: (k -> a -> String) -> Bool -> [String] -> [String] -> Map k a -> ShowS
showsTree showelem wide lbars rbars t
  = case t of
      Tip -> showsBars lbars . showString "|\n"
      Bin _ kx x Tip Tip
          -> showsBars lbars . showString (showelem kx x) . showString "\n"
      Bin _ kx x l r
          -> showsTree showelem wide (withBar rbars) (withEmpty rbars) r .
             showWide wide rbars .
             showsBars lbars . showString (showelem kx x) . showString "\n" .
             showWide wide lbars .
             showsTree showelem wide (withEmpty lbars) (withBar lbars) l

{-@ Decrease showsTreeHang 4 @-}
showsTreeHang :: (k -> a -> String) -> Bool -> [String] -> Map k a -> ShowS
showsTreeHang showelem wide bars t
  = case t of
      Tip -> showsBars bars . showString "|\n"
      Bin _ kx x Tip Tip
          -> showsBars bars . showString (showelem kx x) . showString "\n"
      Bin _ kx x l r
          -> showsBars bars . showString (showelem kx x) . showString "\n" .
             showWide wide bars .
             showsTreeHang showelem wide (withBar bars) l .
             showWide wide bars .
             showsTreeHang showelem wide (withEmpty bars) r

showWide :: Bool -> [String] -> String -> String
showWide wide bars
  | wide      = showString (concat (reverse bars)) . showString "|\n"
  | otherwise = id

showsBars :: [String] -> ShowS
showsBars bars
  = case bars of
      [] -> id
      _  -> showString (concat (reverse (tail bars))) . showString node

node :: String
node           = "+--"

withBar, withEmpty :: [String] -> [String]
withBar bars   = "|  ":bars
withEmpty bars = "   ":bars

{--------------------------------------------------------------------
  Typeable
--------------------------------------------------------------------}

-- LIQUID #include "Typeable.h"
-- LIQUID INSTANCE_TYPEABLE2(Map,mapTc,"Map")

{--------------------------------------------------------------------
  Assertions
--------------------------------------------------------------------}
-- | /O(n)/. Test if the internal map structure is valid.
--
-- > valid (fromAscList [(3,"b"), (5,"a")]) == True
-- > valid (fromAscList [(5,"a"), (3,"b")]) == False

valid :: Ord k => Map k a -> Bool
valid t
  = balanced t && ordered t && validsize t

ordered :: Ord a => Map a b -> Bool
ordered t
  = bounded (const True) (const True) t
  where
    bounded lo hi t'
      = case t' of
          Tip              -> True
          Bin _ kx _ l r  -> (lo kx) && (hi kx) && bounded lo (<kx) l && bounded (>kx) hi r

-- | Exported only for "Debug.QuickCheck"
balanced :: Map k a -> Bool
balanced t
  = case t of
      Tip            -> True
      Bin _ _ _ l r  -> (size l + size r <= 1 || (size l <= delta*size r && size r <= delta*size l)) &&
                        balanced l && balanced r

validsize :: Map a b -> Bool
validsize t
  = (realsize t == Just (size t))
  where
    realsize t'
      = case t' of
          Tip            -> Just 0
          Bin sz _ _ l r -> case (realsize l,realsize r) of
                            (Just n,Just m)  | n+m+1 == sz  -> Just sz
                            _                               -> Nothing

{--------------------------------------------------------------------
  Utilities
--------------------------------------------------------------------}
foldlStrict :: (a -> b -> a) -> a -> [b] -> a
foldlStrict f = go
  where
    go z []     = z
    go z (x:xs) = let z' = f z x in z' `seq` go z' xs
{-# INLINE foldlStrict #-}
