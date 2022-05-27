{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE CPP, NoImplicitPrelude, MagicHash #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.List
-- Copyright   :  (c) The University of Glasgow 2001
-- License     :  BSD-style (see the file libraries/base/LICENSE)
-- 
-- Maintainer  :  libraries@haskell.org
-- Stability   :  stable
-- Portability :  portable
--
-- Operations on lists.
--
-----------------------------------------------------------------------------

module Data.List
   (
#ifdef __NHC__
     [] (..)
   ,
#endif

   -- * Basic functions

     (++)              -- :: [a] -> [a] -> [a]
   , head              -- :: [a] -> a
   , last              -- :: [a] -> a
   , tail              -- :: [a] -> [a]
   , init              -- :: [a] -> [a]
   , null              -- :: [a] -> Bool
   , length            -- :: [a] -> Int

   -- * List transformations
   , map               -- :: (a -> b) -> [a] -> [b]
   , reverse           -- :: [a] -> [a]

   , intersperse       -- :: a -> [a] -> [a]
   , intercalate       -- :: [a] -> [[a]] -> [a]
   , transpose         -- :: [[a]] -> [[a]]
   
   , subsequences      -- :: [a] -> [[a]]
   , permutations      -- :: [a] -> [[a]]

   -- * Reducing lists (folds)

   , foldl             -- :: (a -> b -> a) -> a -> [b] -> a
   , foldl'            -- :: (a -> b -> a) -> a -> [b] -> a
   , foldl1            -- :: (a -> a -> a) -> [a] -> a
   , foldl1'           -- :: (a -> a -> a) -> [a] -> a
   , foldr             -- :: (a -> b -> b) -> b -> [a] -> b
   , foldr1            -- :: (a -> a -> a) -> [a] -> a

   -- ** Special folds

   , concat            -- :: [[a]] -> [a]
   , concatMap         -- :: (a -> [b]) -> [a] -> [b]
   , and               -- :: [Bool] -> Bool
   , or                -- :: [Bool] -> Bool
   , any               -- :: (a -> Bool) -> [a] -> Bool
   , all               -- :: (a -> Bool) -> [a] -> Bool
   , sum               -- :: (Num a) => [a] -> a
   , product           -- :: (Num a) => [a] -> a
   , maximum           -- :: (Ord a) => [a] -> a
   , minimum           -- :: (Ord a) => [a] -> a

   -- * Building lists

   -- ** Scans
   , scanl             -- :: (a -> b -> a) -> a -> [b] -> [a]
   , scanl1            -- :: (a -> a -> a) -> [a] -> [a]
   , scanr             -- :: (a -> b -> b) -> b -> [a] -> [b]
   , scanr1            -- :: (a -> a -> a) -> [a] -> [a]

   -- ** Accumulating maps
   , mapAccumL         -- :: (a -> b -> (a,c)) -> a -> [b] -> (a,[c])
   , mapAccumR         -- :: (a -> b -> (a,c)) -> a -> [b] -> (a,[c])

   -- ** Infinite lists
   , iterate           -- :: (a -> a) -> a -> [a]
   , repeat            -- :: a -> [a]
   , replicate         -- :: Int -> a -> [a]
   , cycle             -- :: [a] -> [a]

   -- ** Unfolding
   , unfoldr           -- :: (b -> Maybe (a, b)) -> b -> [a]

   -- * Sublists

   -- ** Extracting sublists
   , take              -- :: Int -> [a] -> [a]
   , drop              -- :: Int -> [a] -> [a]
   , splitAt           -- :: Int -> [a] -> ([a], [a])

   , takeWhile         -- :: (a -> Bool) -> [a] -> [a]
   , dropWhile         -- :: (a -> Bool) -> [a] -> [a]
   , dropWhileEnd      -- :: (a -> Bool) -> [a] -> [a]
   , span              -- :: (a -> Bool) -> [a] -> ([a], [a])
   , break             -- :: (a -> Bool) -> [a] -> ([a], [a])

   , stripPrefix       -- :: Eq a => [a] -> [a] -> Maybe [a]

   , group             -- :: Eq a => [a] -> [[a]]

   , inits             -- :: [a] -> [[a]]
   , tails             -- :: [a] -> [[a]]

   -- ** Predicates
   , isPrefixOf        -- :: (Eq a) => [a] -> [a] -> Bool
   , isSuffixOf        -- :: (Eq a) => [a] -> [a] -> Bool
   , isInfixOf         -- :: (Eq a) => [a] -> [a] -> Bool

   -- * Searching lists

   -- ** Searching by equality
   , elem              -- :: a -> [a] -> Bool
   , notElem           -- :: a -> [a] -> Bool
   , lookup            -- :: (Eq a) => a -> [(a,b)] -> Maybe b

   -- ** Searching with a predicate
   , find              -- :: (a -> Bool) -> [a] -> Maybe a
   , filter            -- :: (a -> Bool) -> [a] -> [a]
   , partition         -- :: (a -> Bool) -> [a] -> ([a], [a])

   -- * Indexing lists
   -- | These functions treat a list @xs@ as a indexed collection,
   -- with indices ranging from 0 to @'length' xs - 1@.

   , (!!)              -- :: [a] -> Int -> a

   , elemIndex         -- :: (Eq a) => a -> [a] -> Maybe Int
   , elemIndices       -- :: (Eq a) => a -> [a] -> [Int]

   , findIndex         -- :: (a -> Bool) -> [a] -> Maybe Int
   , findIndices       -- :: (a -> Bool) -> [a] -> [Int]

   -- * Zipping and unzipping lists

   , zip               -- :: [a] -> [b] -> [(a,b)]
   , zip3
   , zip4, zip5, zip6, zip7

   , zipWith           -- :: (a -> b -> c) -> [a] -> [b] -> [c]
   , zipWith3
   , zipWith4, zipWith5, zipWith6, zipWith7

   , unzip             -- :: [(a,b)] -> ([a],[b])
   , unzip3
   , unzip4, unzip5, unzip6, unzip7

   -- * Special lists

   -- ** Functions on strings
   , lines             -- :: String   -> [String]
   , words             -- :: String   -> [String]
   , unlines           -- :: [String] -> String
   , unwords           -- :: [String] -> String

   -- ** \"Set\" operations

   , nub               -- :: (Eq a) => [a] -> [a]

   , delete            -- :: (Eq a) => a -> [a] -> [a]
   , (\\)              -- :: (Eq a) => [a] -> [a] -> [a]

   , union             -- :: (Eq a) => [a] -> [a] -> [a]
   , intersect         -- :: (Eq a) => [a] -> [a] -> [a]

   -- ** Ordered lists
   , sort              -- :: (Ord a) => [a] -> [a]
   , insert            -- :: (Ord a) => a -> [a] -> [a]

   -- * Generalized functions

   -- ** The \"@By@\" operations
   -- | By convention, overloaded functions have a non-overloaded
   -- counterpart whose name is suffixed with \`@By@\'.
   --
   -- It is often convenient to use these functions together with
   -- 'Data.Function.on', for instance @'sortBy' ('compare'
   -- \`on\` 'fst')@.

   -- *** User-supplied equality (replacing an @Eq@ context)
   -- | The predicate is assumed to define an equivalence.
   , nubBy             -- :: (a -> a -> Bool) -> [a] -> [a]
   , deleteBy          -- :: (a -> a -> Bool) -> a -> [a] -> [a]
   , deleteFirstsBy    -- :: (a -> a -> Bool) -> [a] -> [a] -> [a]
   , unionBy           -- :: (a -> a -> Bool) -> [a] -> [a] -> [a]
   , intersectBy       -- :: (a -> a -> Bool) -> [a] -> [a] -> [a]
   , groupBy           -- :: (a -> a -> Bool) -> [a] -> [[a]]

   -- *** User-supplied comparison (replacing an @Ord@ context)
   -- | The function is assumed to define a total ordering.
   , sortBy            -- :: (a -> a -> Ordering) -> [a] -> [a]
   , insertBy          -- :: (a -> a -> Ordering) -> a -> [a] -> [a]
   , maximumBy         -- :: (a -> a -> Ordering) -> [a] -> a
   , minimumBy         -- :: (a -> a -> Ordering) -> [a] -> a

   -- ** The \"@generic@\" operations
   -- | The prefix \`@generic@\' indicates an overloaded function that
   -- is a generalized version of a "Prelude" function.

   , genericLength     -- :: (Integral a) => [b] -> a
   , genericTake       -- :: (Integral a) => a -> [b] -> [b]
   , genericDrop       -- :: (Integral a) => a -> [b] -> [b]
   , genericSplitAt    -- :: (Integral a) => a -> [b] -> ([b], [b])
   , genericIndex      -- :: (Integral a) => [b] -> a -> b
   , genericReplicate  -- :: (Integral a) => a -> b -> [b]

   ) where

#ifdef __NHC__
import Prelude
#endif

import Data.Maybe
import Data.Char        ( isSpace )

#ifdef __GLASGOW_HASKELL__
import GHC.Num
import GHC.Real
import GHC.List
import GHC.Base
#endif

infix 5 \\ -- comment to fool cpp

-- -----------------------------------------------------------------------------
-- List functions

-- | The 'dropWhileEnd' function drops the largest suffix of a list
-- in which the given predicate holds for all elements.  For example:
--
-- > dropWhileEnd isSpace "foo\n" == "foo"
-- > dropWhileEnd isSpace "foo bar" == "foo bar"
-- > dropWhileEnd isSpace ("foo\n" ++ undefined) == "foo" ++ undefined

dropWhileEnd :: (a -> Bool) -> [a] -> [a]
dropWhileEnd p = foldr (\x xs -> if p x && null xs then [] else x : xs) []

-- | The 'stripPrefix' function drops the given prefix from a list.
-- It returns 'Nothing' if the list did not start with the prefix
-- given, or 'Just' the list after the prefix, if it does.
--
-- > stripPrefix "foo" "foobar" == Just "bar"
-- > stripPrefix "foo" "foo" == Just ""
-- > stripPrefix "foo" "barfoo" == Nothing
-- > stripPrefix "foo" "barfoobaz" == Nothing
stripPrefix :: Eq a => [a] -> [a] -> Maybe [a]
stripPrefix [] ys = Just ys
stripPrefix (x:xs) (y:ys)
 | x == y = stripPrefix xs ys
stripPrefix _ _ = Nothing

-- | The 'elemIndex' function returns the index of the first element
-- in the given list which is equal (by '==') to the query element,
-- or 'Nothing' if there is no such element.
elemIndex       :: Eq a => a -> [a] -> Maybe Int
elemIndex x     = findIndex (x==)

-- | The 'elemIndices' function extends 'elemIndex', by returning the
-- indices of all elements equal to the query element, in ascending order.
elemIndices     :: Eq a => a -> [a] -> [Int]
elemIndices x   = findIndices (x==)

-- | The 'find' function takes a predicate and a list and returns the
-- first element in the list matching the predicate, or 'Nothing' if
-- there is no such element.
find            :: (a -> Bool) -> [a] -> Maybe a
find p          = listToMaybe . filter p

-- | The 'findIndex' function takes a predicate and a list and returns
-- the index of the first element in the list satisfying the predicate,
-- or 'Nothing' if there is no such element.
findIndex       :: (a -> Bool) -> [a] -> Maybe Int
findIndex p     = listToMaybe . findIndices p

-- | The 'findIndices' function extends 'findIndex', by returning the
-- indices of all elements satisfying the predicate, in ascending order.
findIndices      :: (a -> Bool) -> [a] -> [Int]

#if defined(USE_REPORT_PRELUDE) || !defined(__GLASGOW_HASKELL__)
findIndices p xs = [ i | (x,i) <- zip xs [0..], p x]
#else
-- Efficient definition
findIndices p ls = loop 0 ls
                 where
                   loop _ [] = []
                   loop n (x:xs) | p x       = n : loop (n + 1) xs
                                 | otherwise = loop (n + 1) xs
#endif  /* USE_REPORT_PRELUDE */

-- | The 'isPrefixOf' function takes two lists and returns 'True'
-- iff the first list is a prefix of the second.
isPrefixOf              :: (Eq a) => [a] -> [a] -> Bool
isPrefixOf [] _         =  True
isPrefixOf _  []        =  False
isPrefixOf (x:xs) (y:ys)=  x == y && isPrefixOf xs ys

-- | The 'isSuffixOf' function takes two lists and returns 'True'
-- iff the first list is a suffix of the second.
-- Both lists must be finite.
isSuffixOf              :: (Eq a) => [a] -> [a] -> Bool
isSuffixOf x y          =  reverse x `isPrefixOf` reverse y

-- | The 'isInfixOf' function takes two lists and returns 'True'
-- iff the first list is contained, wholly and intact,
-- anywhere within the second.
--
-- Example:
--
-- >isInfixOf "Haskell" "I really like Haskell." == True
-- >isInfixOf "Ial" "I really like Haskell." == False
isInfixOf               :: (Eq a) => [a] -> [a] -> Bool
isInfixOf needle haystack = any (isPrefixOf needle) (tails haystack)

-- | /O(n^2)/. The 'nub' function removes duplicate elements from a list.
-- In particular, it keeps only the first occurrence of each element.
-- (The name 'nub' means \`essence\'.)
-- It is a special case of 'nubBy', which allows the programmer to supply
-- their own equality test.
nub                     :: (Eq a) => [a] -> [a]
#ifdef USE_REPORT_PRELUDE
nub                     =  nubBy (==)
#else
-- stolen from HBC
nub l                   = nub' l []             -- '
  where
    nub' [] _           = []                    -- '
    nub' (x:xs) ls                              -- '
        | x `elem` ls   = nub' xs ls            -- '
        | otherwise     = x : nub' xs (x:ls)    -- '
#endif

-- | The 'nubBy' function behaves just like 'nub', except it uses a
-- user-supplied equality predicate instead of the overloaded '=='
-- function.
nubBy                   :: (a -> a -> Bool) -> [a] -> [a]
#ifdef USE_REPORT_PRELUDE
nubBy eq []             =  []
nubBy eq (x:xs)         =  x : nubBy eq (filter (\ y -> not (eq x y)) xs)
#else
nubBy eq l              = nubBy' l []
  where
    nubBy' [] _          = []
    nubBy' (y:ys) xs
       | elem_by eq y xs = nubBy' ys xs
       | otherwise       = y : nubBy' ys (y:xs)

-- Not exported:
-- Note that we keep the call to `eq` with arguments in the
-- same order as in the reference implementation
-- 'xs' is the list of things we've seen so far, 
-- 'y' is the potential new element
elem_by :: (a -> a -> Bool) -> a -> [a] -> Bool
elem_by _  _ []         =  False
elem_by eq y (x:xs)     =  y `eq` x || elem_by eq y xs
#endif


-- | 'delete' @x@ removes the first occurrence of @x@ from its list argument.
-- For example,
--
-- > delete 'a' "banana" == "bnana"
--
-- It is a special case of 'deleteBy', which allows the programmer to
-- supply their own equality test.

delete                  :: (Eq a) => a -> [a] -> [a]
delete                  =  deleteBy (==)

-- | The 'deleteBy' function behaves like 'delete', but takes a
-- user-supplied equality predicate.
deleteBy                :: (a -> a -> Bool) -> a -> [a] -> [a]
deleteBy _  _ []        = []
deleteBy eq x (y:ys)    = if x `eq` y then ys else y : deleteBy eq x ys

-- | The '\\' function is list difference (non-associative).
-- In the result of @xs@ '\\' @ys@, the first occurrence of each element of
-- @ys@ in turn (if any) has been removed from @xs@.  Thus
--
-- > (xs ++ ys) \\ xs == ys.
--
-- It is a special case of 'deleteFirstsBy', which allows the programmer
-- to supply their own equality test.

(\\)                    :: (Eq a) => [a] -> [a] -> [a]
(\\)                    =  foldl (flip delete)

-- | The 'union' function returns the list union of the two lists.
-- For example,
--
-- > "dog" `union` "cow" == "dogcw"
--
-- Duplicates, and elements of the first list, are removed from the
-- the second list, but if the first list contains duplicates, so will
-- the result.
-- It is a special case of 'unionBy', which allows the programmer to supply
-- their own equality test.

union                   :: (Eq a) => [a] -> [a] -> [a]
union                   = unionBy (==)

-- | The 'unionBy' function is the non-overloaded version of 'union'.
unionBy                 :: (a -> a -> Bool) -> [a] -> [a] -> [a]
unionBy eq xs ys        =  xs ++ foldl (flip (deleteBy eq)) (nubBy eq ys) xs

-- | The 'intersect' function takes the list intersection of two lists.
-- For example,
--
-- > [1,2,3,4] `intersect` [2,4,6,8] == [2,4]
--
-- If the first list contains duplicates, so will the result.
--
-- > [1,2,2,3,4] `intersect` [6,4,4,2] == [2,2,4]
--
-- It is a special case of 'intersectBy', which allows the programmer to
-- supply their own equality test.

intersect               :: (Eq a) => [a] -> [a] -> [a]
intersect               =  intersectBy (==)

-- | The 'intersectBy' function is the non-overloaded version of 'intersect'.
intersectBy             :: (a -> a -> Bool) -> [a] -> [a] -> [a]
intersectBy _  [] _     =  []
intersectBy _  _  []    =  []
intersectBy eq xs ys    =  [x | x <- xs, any (eq x) ys]

-- | The 'intersperse' function takes an element and a list and
-- \`intersperses\' that element between the elements of the list.
-- For example,
--
-- > intersperse ',' "abcde" == "a,b,c,d,e"

intersperse             :: a -> [a] -> [a]
intersperse _   []      = []
intersperse sep (x:xs)  = x : prependToAll sep xs


-- Not exported:
-- We want to make every element in the 'intersperse'd list available
-- as soon as possible to avoid space leaks. Experiments suggested that
-- a separate top-level helper is more efficient than a local worker.
prependToAll            :: a -> [a] -> [a]
prependToAll _   []     = []
prependToAll sep (x:xs) = sep : x : prependToAll sep xs

-- | 'intercalate' @xs xss@ is equivalent to @('concat' ('intersperse' xs xss))@.
-- It inserts the list @xs@ in between the lists in @xss@ and concatenates the
-- result.
intercalate :: [a] -> [[a]] -> [a]
intercalate xs xss = concat (intersperse xs xss)

-- | The 'transpose' function transposes the rows and columns of its argument.
-- For example,
--
-- > transpose [[1,2,3],[4,5,6]] == [[1,4],[2,5],[3,6]]

{-@ measure sumLens :: [[a]] -> GHC.Types.Int
      sumLens ([])   = 0
      sumLens (c:cs) = (len c) + (sumLens cs)
  @-}
{-@ invariant {v:[[a]] | (sumLens v) >= 0} @-}
{-@ qualif SumLensEq(v:List List a, x:List List a): (sumLens v) = (sumLens x) @-}
{-@ qualif SumLensEq(v:List List a, x:List a): (sumLens v) = (len x) @-}
{-@ qualif SumLensLe(v:List List a, x:List List a): (sumLens v) <= (sumLens x) @-}

{-@ transpose :: xs:[[a]] -> [[a]] / [(sumLens xs)+(len xs)] @-}
transpose               :: [[a]] -> [[a]]
transpose []             = []
transpose ([]   : xss)   = transpose xss
transpose ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : transpose (xs : [ t | (_:t) <- xss])

-- | The 'partition' function takes a predicate a list and returns
-- the pair of lists of elements which do and do not satisfy the
-- predicate, respectively; i.e.,
--
-- > partition p xs == (filter p xs, filter (not . p) xs)

partition               :: (a -> Bool) -> [a] -> ([a],[a])
{-# INLINE partition #-}
partition p xs = foldr (select p) ([],[]) xs

select :: (a -> Bool) -> a -> ([a], [a]) -> ([a], [a])
select p x ~(ts,fs) | p x       = (x:ts,fs)
                    | otherwise = (ts, x:fs)

-- | The 'mapAccumL' function behaves like a combination of 'map' and
-- 'foldl'; it applies a function to each element of a list, passing
-- an accumulating parameter from left to right, and returning a final
-- value of this accumulator together with the new list.
mapAccumL :: (acc -> x -> (acc, y)) -- Function of elt of input list
                                    -- and accumulator, returning new
                                    -- accumulator and elt of result list
          -> acc            -- Initial accumulator 
          -> [x]            -- Input list
          -> (acc, [y])     -- Final accumulator and result list
mapAccumL _ s []        =  (s, [])
mapAccumL f s (x:xs)    =  (s'',y:ys)
                           where (s', y ) = f s x
                                 (s'',ys) = mapAccumL f s' xs

-- | The 'mapAccumR' function behaves like a combination of 'map' and
-- 'foldr'; it applies a function to each element of a list, passing
-- an accumulating parameter from right to left, and returning a final
-- value of this accumulator together with the new list.
mapAccumR :: (acc -> x -> (acc, y))     -- Function of elt of input list
                                        -- and accumulator, returning new
                                        -- accumulator and elt of result list
            -> acc              -- Initial accumulator
            -> [x]              -- Input list
            -> (acc, [y])               -- Final accumulator and result list
mapAccumR _ s []        =  (s, [])
mapAccumR f s (x:xs)    =  (s'', y:ys)
                           where (s'',y ) = f s' x
                                 (s', ys) = mapAccumR f s xs

-- | The 'insert' function takes an element and a list and inserts the
-- element into the list at the last position where it is still less
-- than or equal to the next element.  In particular, if the list
-- is sorted before the call, the result will also be sorted.
-- It is a special case of 'insertBy', which allows the programmer to
-- supply their own comparison function.
insert :: Ord a => a -> [a] -> [a]
insert e ls = insertBy (compare) e ls

-- | The non-overloaded version of 'insert'.
insertBy :: (a -> a -> Ordering) -> a -> [a] -> [a]
insertBy _   x [] = [x]
insertBy cmp x ys@(y:ys')
 = case cmp x y of
     GT -> y : insertBy cmp x ys'
     _  -> x : ys

#ifdef __GLASGOW_HASKELL__

-- | 'maximum' returns the maximum value from a list,
-- which must be non-empty, finite, and of an ordered type.
-- It is a special case of 'Data.List.maximumBy', which allows the
-- programmer to supply their own comparison function.
{-@ maximum             :: (Ord a) => {v:[a]|(len v) > 0} -> a @-}
maximum                 :: (Ord a) => [a] -> a
maximum []              =  errorEmptyList "maximum"
maximum xs              =  foldl1 max xs

{-# RULES
  "maximumInt"     maximum = (strictMaximum :: [Int]     -> Int);
  "maximumInteger" maximum = (strictMaximum :: [Integer] -> Integer)
 #-}

-- We can't make the overloaded version of maximum strict without
-- changing its semantics (max might not be strict), but we can for
-- the version specialised to 'Int'.
{-@ strictMaximum       :: (Ord a) => {v:[a]|(len v) > 0} -> a @-}
strictMaximum           :: (Ord a) => [a] -> a
strictMaximum []        =  errorEmptyList "maximum"
strictMaximum xs        =  foldl1' max xs

-- | 'minimum' returns the minimum value from a list,
-- which must be non-empty, finite, and of an ordered type.
-- It is a special case of 'Data.List.minimumBy', which allows the
-- programmer to supply their own comparison function.
{-@ minimum             :: (Ord a) => {v:[a]|(len v) > 0} -> a @-}
minimum                 :: (Ord a) => [a] -> a
minimum []              =  errorEmptyList "minimum"
minimum xs              =  foldl1 min xs

{-# RULES
  "minimumInt"     minimum = (strictMinimum :: [Int]     -> Int);
  "minimumInteger" minimum = (strictMinimum :: [Integer] -> Integer)
 #-}

{-@ strictMinimum       :: (Ord a) => {v:[a]| (len v) > 0 } -> a @-}
strictMinimum           :: (Ord a) => [a] -> a
strictMinimum []        =  errorEmptyList "minimum"
strictMinimum xs        =  foldl1' min xs

#endif /* __GLASGOW_HASKELL__ */

-- | The 'maximumBy' function takes a comparison function and a list
-- and returns the greatest element of the list by the comparison function.
-- The list must be finite and non-empty.
maximumBy               :: (a -> a -> Ordering) -> [a] -> a
maximumBy _ []          =  error "List.maximumBy: empty list"
maximumBy cmp xs        =  foldl1 maxBy xs
                        where
                           maxBy x y = case cmp x y of
                                       GT -> x
                                       _  -> y

-- | The 'minimumBy' function takes a comparison function and a list
-- and returns the least element of the list by the comparison function.
-- The list must be finite and non-empty.
minimumBy               :: (a -> a -> Ordering) -> [a] -> a
minimumBy _ []          =  error "List.minimumBy: empty list"
minimumBy cmp xs        =  foldl1 minBy xs
                        where
                           minBy x y = case cmp x y of
                                       GT -> y
                                       _  -> x

-- | The 'genericLength' function is an overloaded version of 'length'.  In
-- particular, instead of returning an 'Int', it returns any type which is
-- an instance of 'Num'.  It is, however, less efficient than 'length'.
genericLength           :: (Num i) => [b] -> i
genericLength []        =  0
genericLength (_:l)     =  1 + genericLength l

{-# RULES
  "genericLengthInt"     genericLength = (strictGenericLength :: [a] -> Int);
  "genericLengthInteger" genericLength = (strictGenericLength :: [a] -> Integer);
 #-}

{-@ strictGenericLength :: (Num i) => [b] -> i @-}
strictGenericLength     :: (Num i) => [b] -> i
strictGenericLength l   =  gl l 0
                        where
                           gl [] a     = a
                           gl (_:xs) a = let a' = a + 1 in a' `seq` gl xs a'

-- | The 'genericTake' function is an overloaded version of 'take', which
-- accepts any 'Integral' value as the number of elements to take.
genericTake             :: (Integral i) => i -> [a] -> [a]
genericTake n _ | n <= 0 = []
genericTake _ []        =  []
genericTake n (x:xs)    =  x : genericTake (n-1) xs

-- | The 'genericDrop' function is an overloaded version of 'drop', which
-- accepts any 'Integral' value as the number of elements to drop.
genericDrop             :: (Integral i) => i -> [a] -> [a]
genericDrop n xs | n <= 0 = xs
genericDrop _ []        =  []
genericDrop n (_:xs)    =  genericDrop (n-1) xs


-- | The 'genericSplitAt' function is an overloaded version of 'splitAt', which
-- accepts any 'Integral' value as the position at which to split.
genericSplitAt          :: (Integral i) => i -> [b] -> ([b],[b])
genericSplitAt n xs | n <= 0 =  ([],xs)
genericSplitAt _ []     =  ([],[])
genericSplitAt n (x:xs) =  (x:xs',xs'') where
    (xs',xs'') = genericSplitAt (n-1) xs

-- | The 'genericIndex' function is an overloaded version of '!!', which
-- accepts any 'Integral' value as the index.
genericIndex :: (Integral a) => [b] -> a -> b
genericIndex (x:_)  0 = x
genericIndex (_:xs) n
 | n > 0     = genericIndex xs (n-1)
 | otherwise = error "List.genericIndex: negative argument."
genericIndex _ _      = error "List.genericIndex: index too large."

-- | The 'genericReplicate' function is an overloaded version of 'replicate',
-- which accepts any 'Integral' value as the number of repetitions to make.
genericReplicate        :: (Integral i) => i -> a -> [a]
genericReplicate n x    =  genericTake n (repeat x)

-- | The 'zip4' function takes four lists and returns a list of
-- quadruples, analogous to 'zip'.
zip4                    :: [a] -> [b] -> [c] -> [d] -> [(a,b,c,d)]
zip4                    =  zipWith4 (,,,)

-- | The 'zip5' function takes five lists and returns a list of
-- five-tuples, analogous to 'zip'.
zip5                    :: [a] -> [b] -> [c] -> [d] -> [e] -> [(a,b,c,d,e)]
zip5                    =  zipWith5 (,,,,)

-- | The 'zip6' function takes six lists and returns a list of six-tuples,
-- analogous to 'zip'.
zip6                    :: [a] -> [b] -> [c] -> [d] -> [e] -> [f] ->
                              [(a,b,c,d,e,f)]
zip6                    =  zipWith6 (,,,,,)

-- | The 'zip7' function takes seven lists and returns a list of
-- seven-tuples, analogous to 'zip'.
zip7                    :: [a] -> [b] -> [c] -> [d] -> [e] -> [f] ->
                              [g] -> [(a,b,c,d,e,f,g)]
zip7                    =  zipWith7 (,,,,,,)

-- | The 'zipWith4' function takes a function which combines four
-- elements, as well as four lists and returns a list of their point-wise
-- combination, analogous to 'zipWith'.
zipWith4                :: (a->b->c->d->e) -> [a]->[b]->[c]->[d]->[e]
zipWith4 z (a:as) (b:bs) (c:cs) (d:ds)
                        =  z a b c d : zipWith4 z as bs cs ds
zipWith4 _ _ _ _ _      =  []

-- | The 'zipWith5' function takes a function which combines five
-- elements, as well as five lists and returns a list of their point-wise
-- combination, analogous to 'zipWith'.
zipWith5                :: (a->b->c->d->e->f) ->
                           [a]->[b]->[c]->[d]->[e]->[f]
zipWith5 z (a:as) (b:bs) (c:cs) (d:ds) (e:es)
                        =  z a b c d e : zipWith5 z as bs cs ds es
zipWith5 _ _ _ _ _ _    = []

-- | The 'zipWith6' function takes a function which combines six
-- elements, as well as six lists and returns a list of their point-wise
-- combination, analogous to 'zipWith'.
zipWith6                :: (a->b->c->d->e->f->g) ->
                           [a]->[b]->[c]->[d]->[e]->[f]->[g]
zipWith6 z (a:as) (b:bs) (c:cs) (d:ds) (e:es) (f:fs)
                        =  z a b c d e f : zipWith6 z as bs cs ds es fs
zipWith6 _ _ _ _ _ _ _  = []

-- | The 'zipWith7' function takes a function which combines seven
-- elements, as well as seven lists and returns a list of their point-wise
-- combination, analogous to 'zipWith'.
zipWith7                :: (a->b->c->d->e->f->g->h) ->
                           [a]->[b]->[c]->[d]->[e]->[f]->[g]->[h]
zipWith7 z (a:as) (b:bs) (c:cs) (d:ds) (e:es) (f:fs) (g:gs)
                   =  z a b c d e f g : zipWith7 z as bs cs ds es fs gs
zipWith7 _ _ _ _ _ _ _ _ = []

-- | The 'unzip4' function takes a list of quadruples and returns four
-- lists, analogous to 'unzip'.
unzip4                  :: [(a,b,c,d)] -> ([a],[b],[c],[d])
unzip4                  =  foldr (\(a,b,c,d) ~(as,bs,cs,ds) ->
                                        (a:as,b:bs,c:cs,d:ds))
                                 ([],[],[],[])

-- | The 'unzip5' function takes a list of five-tuples and returns five
-- lists, analogous to 'unzip'.
unzip5                  :: [(a,b,c,d,e)] -> ([a],[b],[c],[d],[e])
unzip5                  =  foldr (\(a,b,c,d,e) ~(as,bs,cs,ds,es) ->
                                        (a:as,b:bs,c:cs,d:ds,e:es))
                                 ([],[],[],[],[])

-- | The 'unzip6' function takes a list of six-tuples and returns six
-- lists, analogous to 'unzip'.
unzip6                  :: [(a,b,c,d,e,f)] -> ([a],[b],[c],[d],[e],[f])
unzip6                  =  foldr (\(a,b,c,d,e,f) ~(as,bs,cs,ds,es,fs) ->
                                        (a:as,b:bs,c:cs,d:ds,e:es,f:fs))
                                 ([],[],[],[],[],[])

-- | The 'unzip7' function takes a list of seven-tuples and returns
-- seven lists, analogous to 'unzip'.
unzip7          :: [(a,b,c,d,e,f,g)] -> ([a],[b],[c],[d],[e],[f],[g])
unzip7          =  foldr (\(a,b,c,d,e,f,g) ~(as,bs,cs,ds,es,fs,gs) ->
                                (a:as,b:bs,c:cs,d:ds,e:es,f:fs,g:gs))
                         ([],[],[],[],[],[],[])


-- | The 'deleteFirstsBy' function takes a predicate and two lists and
-- returns the first list with the first occurrence of each element of
-- the second list removed.
deleteFirstsBy          :: (a -> a -> Bool) -> [a] -> [a] -> [a]
deleteFirstsBy eq       =  foldl (flip (deleteBy eq))

-- | The 'group' function takes a list and returns a list of lists such
-- that the concatenation of the result is equal to the argument.  Moreover,
-- each sublist in the result contains only equal elements.  For example,
--
-- > group "Mississippi" = ["M","i","ss","i","ss","i","pp","i"]
--
-- It is a special case of 'groupBy', which allows the programmer to supply
-- their own equality test.
group                   :: Eq a => [a] -> [[a]]
group                   =  groupBy (==)

-- | The 'groupBy' function is the non-overloaded version of 'group'.
groupBy                 :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy _  []           =  []
groupBy eq (x:xs)       =  (x:ys) : groupBy eq zs
                           where (ys,zs) = span (eq x) xs

-- | The 'inits' function returns all initial segments of the argument,
-- shortest first.  For example,
--
-- > inits "abc" == ["","a","ab","abc"]
--
-- Note that 'inits' has the following strictness property:
-- @inits _|_ = [] : _|_@
{-@ inits               :: [a] -> {v:[[a]] | (len v) > 0} @-}
inits                   :: [a] -> [[a]]
inits xs                =  [] : case xs of
                                  []      -> []
                                  x : xs' -> map (x :) (inits xs')

-- | The 'tails' function returns all final segments of the argument,
-- longest first.  For example,
--
-- > tails "abc" == ["abc", "bc", "c",""]
--
-- Note that 'tails' has the following strictness property:
-- @tails _|_ = _|_ : _|_@
tails                   :: [a] -> [[a]]
tails xs                =  xs : case xs of
                                  []      -> []
                                  _ : xs' -> tails xs'

-- | The 'subsequences' function returns the list of all subsequences of the argument.
--
-- > subsequences "abc" == ["","a","b","ab","c","ac","bc","abc"]
subsequences            :: [a] -> [[a]]
subsequences xs         =  [] : nonEmptySubsequences xs

-- | The 'nonEmptySubsequences' function returns the list of all subsequences of the argument,
--   except for the empty list.
--
-- > nonEmptySubsequences "abc" == ["a","b","ab","c","ac","bc","abc"]
nonEmptySubsequences         :: [a] -> [[a]]
nonEmptySubsequences []      =  []
nonEmptySubsequences (x:xs)  =  [x] : foldr f [] (nonEmptySubsequences xs)
  where f ys r = ys : (x : ys) : r


-- | The 'permutations' function returns the list of all permutations of the argument.
--
-- > permutations "abc" == ["abc","bac","cba","bca","cab","acb"]

{-@ permutations :: ts:[a] -> [[a]] / [(len ts), 1, 0] @-}
permutations            :: [a] -> [[a]]
permutations xs0        =  xs0 : perms xs0 []


{-@ perms :: ts:[a] -> is:[a] -> [[a]] / [((len ts)+(len is)), 0, (len ts)] @-}
perms :: [a] -> [a] -> [[a]]
perms []     _  = []
perms (t:ts) is = foldr interleave (perms ts (t:is)) (permutations is)
      where interleave    xs     r = let (_,zs) = interleave' id xs r in zs
            interleave' _ []     r = (ts, r)
            interleave' f (y:ys) r = let (us,zs) = interleave' (f . (y:)) ys r
                                     in  (y:us, f (t:y:us) : zs)


------------------------------------------------------------------------------
-- Quick Sort algorithm taken from HBC's QSort library.

-- | The 'sort' function implements a stable sorting algorithm.
-- It is a special case of 'sortBy', which allows the programmer to supply
-- their own comparison function.
sort :: (Ord a) => [a] -> [a]

-- | The 'sortBy' function is the non-overloaded version of 'sort'.
sortBy :: (a -> a -> Ordering) -> [a] -> [a]

#ifdef USE_REPORT_PRELUDE
sort = sortBy compare
sortBy cmp = foldr (insertBy cmp) []
#else

{-
GHC's mergesort replaced by a better implementation, 24/12/2009.
This code originally contributed to the nhc12 compiler by Thomas Nordin
in 2002.  Rumoured to have been based on code by Lennart Augustsson, e.g.
    http://www.mail-archive.com/haskell@haskell.org/msg01822.html
and possibly to bear similarities to a 1982 paper by Richard O'Keefe:
"A smooth applicative merge sort".

Benchmarks show it to be often 2x the speed of the previous implementation.
Fixes ticket http://hackage.haskell.org/trac/ghc/ticket/2143
-}

{-@ type OList a = [a] @-}

sort = sortBy compare
sortBy cmp xs = mergeAll cmp $ sequences xs 0
  where
    {-@ decrease sequences  1 2 @-}
    {- LIQUID WITNESS -}
    sequences (a:b:xs) (_::Int)
      | a `cmp` b == GT = descending b [a]  xs 1
      | otherwise       = ascending  b (a:) xs 1
    sequences xs _      = [xs]

    {-@ decrease descending 3 4 @-}
    {- LIQUID WITNESS -}
    descending a as (b:bs) (_::Int)
      | a `cmp` b == GT  = descending b (a:as) bs 1 
    descending a as bs _ = (a:as): sequences bs 0

    {-@ decrease ascending  3 4 @-}
    {- LIQUID WITNESS -}
    ascending a as (b:bs) (_::Int)
      | a `cmp` b /= GT = ascending b (\ys -> as (a:ys)) bs 1
    ascending a as bs _ = as [a]: sequences bs 0

mergeAll cmp []  = []
mergeAll cmp [x] = x
mergeAll cmp xs  = mergeAll cmp (mergePairs cmp xs)

{-@ mergePairs :: (a -> a -> Ordering)
               -> xss:[(OList a)] 
               -> {v:[(OList a)] | (if ((len xss) > 1) then ((len v) < (len xss)) else ((len v) = (len xss) ))}
  @-}
mergePairs :: (a -> a -> Ordering) -> [[a]] -> [[a]]
mergePairs cmp (a:b:xs) = merge cmp a b: mergePairs cmp xs
mergePairs cmp xs       = xs

{-@ merge ::  (a -> a -> Ordering) 
           -> xs:(OList a) 
           -> ys:(OList a)
           -> {v:(OList a) | (len v) = ((len xs) + (len ys))} 
           / [(len xs) + (len ys)] 
  @-}
merge :: (a -> a -> Ordering) -> [a] -> [a] -> [a] 
merge cmp as@(a:as') bs@(b:bs')
  | a `cmp` b == GT = b:merge cmp as  bs'
  | otherwise       = a:merge cmp as' bs
merge _ [] bs        = bs
merge _ as []        = as

{-
sortBy cmp l = mergesort cmp l
sort l = mergesort compare l

Quicksort replaced by mergesort, 14/5/2002.

From: Ian Lynagh <igloo@earth.li>

I am curious as to why the List.sort implementation in GHC is a
quicksort algorithm rather than an algorithm that guarantees n log n
time in the worst case? I have attached a mergesort implementation along
with a few scripts to time it's performance, the results of which are
shown below (* means it didn't finish successfully - in all cases this
was due to a stack overflow).

If I heap profile the random_list case with only 10000 then I see
random_list peaks at using about 2.5M of memory, whereas in the same
program using List.sort it uses only 100k.

Input style     Input length     Sort data     Sort alg    User time
stdin           10000            random_list   sort        2.82
stdin           10000            random_list   mergesort   2.96
stdin           10000            sorted        sort        31.37
stdin           10000            sorted        mergesort   1.90
stdin           10000            revsorted     sort        31.21
stdin           10000            revsorted     mergesort   1.88
stdin           100000           random_list   sort        *
stdin           100000           random_list   mergesort   *
stdin           100000           sorted        sort        *
stdin           100000           sorted        mergesort   *
stdin           100000           revsorted     sort        *
stdin           100000           revsorted     mergesort   *
func            10000            random_list   sort        0.31
func            10000            random_list   mergesort   0.91
func            10000            sorted        sort        19.09
func            10000            sorted        mergesort   0.15
func            10000            revsorted     sort        19.17
func            10000            revsorted     mergesort   0.16
func            100000           random_list   sort        3.85
func            100000           random_list   mergesort   *
func            100000           sorted        sort        5831.47
func            100000           sorted        mergesort   2.23
func            100000           revsorted     sort        5872.34
func            100000           revsorted     mergesort   2.24

mergesort :: (a -> a -> Ordering) -> [a] -> [a]
mergesort cmp = mergesort' cmp . map wrap

mergesort' :: (a -> a -> Ordering) -> [[a]] -> [a]
mergesort' _   [] = []
mergesort' _   [xs] = xs
mergesort' cmp xss = mergesort' cmp (merge_pairs cmp xss)

merge_pairs :: (a -> a -> Ordering) -> [[a]] -> [[a]]
merge_pairs _   [] = []
merge_pairs _   [xs] = [xs]
merge_pairs cmp (xs:ys:xss) = merge cmp xs ys : merge_pairs cmp xss

merge :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
merge _   [] ys = ys
merge _   xs [] = xs
merge cmp (x:xs) (y:ys)
 = case x `cmp` y of
        GT -> y : merge cmp (x:xs)   ys
        _  -> x : merge cmp    xs (y:ys)

wrap :: a -> [a]
wrap x = [x]



OLDER: qsort version

-- qsort is stable and does not concatenate.
qsort :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
qsort _   []     r = r
qsort _   [x]    r = x:r
qsort cmp (x:xs) r = qpart cmp x xs [] [] r

-- qpart partitions and sorts the sublists
qpart :: (a -> a -> Ordering) -> a -> [a] -> [a] -> [a] -> [a] -> [a]
qpart cmp x [] rlt rge r =
    -- rlt and rge are in reverse order and must be sorted with an
    -- anti-stable sorting
    rqsort cmp rlt (x:rqsort cmp rge r)
qpart cmp x (y:ys) rlt rge r =
    case cmp x y of
        GT -> qpart cmp x ys (y:rlt) rge r
        _  -> qpart cmp x ys rlt (y:rge) r

-- rqsort is as qsort but anti-stable, i.e. reverses equal elements
rqsort :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
rqsort _   []     r = r
rqsort _   [x]    r = x:r
rqsort cmp (x:xs) r = rqpart cmp x xs [] [] r

rqpart :: (a -> a -> Ordering) -> a -> [a] -> [a] -> [a] -> [a] -> [a]
rqpart cmp x [] rle rgt r =
    qsort cmp rle (x:qsort cmp rgt r)
rqpart cmp x (y:ys) rle rgt r =
    case cmp y x of
        GT -> rqpart cmp x ys rle (y:rgt) r
        _  -> rqpart cmp x ys (y:rle) rgt r
-}

#endif /* USE_REPORT_PRELUDE */

-- | The 'unfoldr' function is a \`dual\' to 'foldr': while 'foldr'
-- reduces a list to a summary value, 'unfoldr' builds a list from
-- a seed value.  The function takes the element and returns 'Nothing'
-- if it is done producing the list or returns 'Just' @(a,b)@, in which
-- case, @a@ is a prepended to the list and @b@ is used as the next
-- element in a recursive call.  For example,
--
-- > iterate f == unfoldr (\x -> Just (x, f x))
--
-- In some cases, 'unfoldr' can undo a 'foldr' operation:
--
-- > unfoldr f' (foldr f z xs) == xs
--
-- if the following holds:
--
-- > f' (f x y) = Just (x,y)
-- > f' z       = Nothing
--
-- A simple use of unfoldr:
--
-- > unfoldr (\b -> if b == 0 then Nothing else Just (b, b-1)) 10
-- >  [10,9,8,7,6,5,4,3,2,1]
--
-- LIQUID TERMINATION : 
-- this function can not termination, eg f x = Just (b, b+1) 
{-@ lazy Data.List.unfoldr @-}
unfoldr      :: (b -> Maybe (a, b)) -> b -> [a]
unfoldr f b  =
  case f b of
   Just (a,new_b) -> a : unfoldr f new_b
   Nothing        -> []

-- -----------------------------------------------------------------------------
-- | A strict version of 'foldl'.
foldl'           :: (a -> b -> a) -> a -> [b] -> a
#ifdef __GLASGOW_HASKELL__
foldl' f z0 xs0 = lgo z0 xs0
    where lgo z []     = z
          lgo z (x:xs) = let z' = f z x in z' `seq` lgo z' xs
#else
foldl' f a []     = a
foldl' f a (x:xs) = let a' = f a x in a' `seq` foldl' f a' xs
#endif


#ifdef __GLASGOW_HASKELL__
-- | 'foldl1' is a variant of 'foldl' that has no starting value argument,
-- and thus must be applied to non-empty lists.
{-@ foldl1 :: (a -> a -> a) -> {v:[a] | (len v) > 0} -> a @-}
foldl1                  :: (a -> a -> a) -> [a] -> a
foldl1 f (x:xs)         =  foldl f x xs
foldl1 _ []             =  errorEmptyList "foldl1"
#endif /* __GLASGOW_HASKELL__ */

-- | A strict version of 'foldl1'
{-@ foldl1' :: (a -> a -> a) -> {v:[a] | (len v) > 0} -> a @-}
foldl1'                  :: (a -> a -> a) -> [a] -> a
foldl1' f (x:xs)         =  foldl' f x xs
foldl1' _ []             =  errorEmptyList "foldl1'"

#ifdef __GLASGOW_HASKELL__
-- -----------------------------------------------------------------------------
-- List sum and product

{-# SPECIALISE sum     :: [Int] -> Int #-}
{-# SPECIALISE sum     :: [Integer] -> Integer #-}
{-# SPECIALISE product :: [Int] -> Int #-}
{-# SPECIALISE product :: [Integer] -> Integer #-}
-- | The 'sum' function computes the sum of a finite list of numbers.
sum                     :: (Num a) => [a] -> a
-- | The 'product' function computes the product of a finite list of numbers.
product                 :: (Num a) => [a] -> a
#ifdef USE_REPORT_PRELUDE
sum                     =  foldl (+) 0
product                 =  foldl (*) 1
#else
sum     l       = sum' l 0
  where
    sum' []     a = a
    sum' (x:xs) a = sum' xs (a+x)
product l       = prod l 1
  where
    prod []     a = a
    prod (x:xs) a = prod xs (a*x)
#endif

-- -----------------------------------------------------------------------------
-- Functions on strings

-- | 'lines' breaks a string up into a list of strings at newline
-- characters.  The resulting strings do not contain newlines.
lines                   :: String -> [String]
lines ""                =  []
#ifdef __GLASGOW_HASKELL__
-- Somehow GHC doesn't detect the selector thunks in the below code,
-- so s' keeps a reference to the first line via the pair and we have
-- a space leak (cf. #4334).
-- So we need to make GHC see the selector thunks with a trick.
lines s                 =  cons (case break (== '\n') s of
                                    (l, s') -> (l, case s' of
                                                    []      -> []
                                                    _:s''   -> lines s''))
  where
    cons ~(h, t)        =  h : t
#else
lines s                 =  let (l, s') = break (== '\n') s
                           in  l : case s' of
                                        []      -> []
                                        (_:s'') -> lines s''
#endif

-- | 'unlines' is an inverse operation to 'lines'.
-- It joins lines, after appending a terminating newline to each.
unlines                 :: [String] -> String
#ifdef USE_REPORT_PRELUDE
unlines                 =  concatMap (++ "\n")
#else
-- HBC version (stolen)
-- here's a more efficient version
unlines [] = []
unlines (l:ls) = l ++ '\n' : unlines ls
#endif

-- | 'words' breaks a string up into a list of words, which were delimited
-- by white space.
{-@ lazy words @-}
--LIQUID TODO: this function terminates because dropWhile guarantees that
--             the first character of s' will not be a space, therefore
--             w will not be empty and s'' < s.
words                   :: String -> [String]
words s                 =  case dropWhile {-partain:Char.-}isSpace s of
                                "" -> []
                                s' -> w : words s''
                                      where (w, s'') =
                                             break {-partain:Char.-}isSpace s'

-- | 'unwords' is an inverse operation to 'words'.
-- It joins words with separating spaces.
unwords                 :: [String] -> String
#ifdef USE_REPORT_PRELUDE
unwords []              =  ""
unwords ws              =  foldr1 (\w s -> w ++ ' ':s) ws
#else
-- HBC version (stolen)
-- here's a more efficient version
unwords []              =  ""
unwords [w]             = w
unwords (w:ws)          = w ++ ' ' : unwords ws
#endif

#else  /* !__GLASGOW_HASKELL__ */

errorEmptyList :: String -> a
errorEmptyList fun =
  error ("Prelude." ++ fun ++ ": empty list")

#endif /* !__GLASGOW_HASKELL__ */

