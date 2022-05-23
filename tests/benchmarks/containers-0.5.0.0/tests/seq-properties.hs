import Data.Sequence    -- needs to be compiled with -DTESTING for use here

import Control.Applicative (Applicative(..))
import Control.Arrow ((***))
import Data.Foldable (Foldable(..), toList, all, sum)
import Data.Functor ((<$>), (<$))
import Data.Maybe
import Data.Monoid (Monoid(..))
import Data.Traversable (Traversable(traverse), sequenceA)
import Prelude hiding (
  null, length, take, drop, splitAt,
  foldl, foldl1, foldr, foldr1, scanl, scanl1, scanr, scanr1,
  filter, reverse, replicate, zip, zipWith, zip3, zipWith3,
  all, sum)
import qualified Prelude
import qualified Data.List
import Test.QuickCheck hiding ((><))
import Test.QuickCheck.Poly
import Test.Framework
import Test.Framework.Providers.QuickCheck2


main :: IO ()
main = defaultMainWithOpts
       [ testProperty "fmap" prop_fmap
       , testProperty "(<$)" prop_constmap
       , testProperty "foldr" prop_foldr
       , testProperty "foldr1" prop_foldr1
       , testProperty "foldl" prop_foldl
       , testProperty "foldl1" prop_foldl1
       , testProperty "(==)" prop_equals
       , testProperty "compare" prop_compare
       , testProperty "mappend" prop_mappend
       , testProperty "singleton" prop_singleton
       , testProperty "(<|)" prop_cons
       , testProperty "(|>)" prop_snoc
       , testProperty "(><)" prop_append
       , testProperty "fromList" prop_fromList
       , testProperty "replicate" prop_replicate
       , testProperty "replicateA" prop_replicateA
       , testProperty "replicateM" prop_replicateM
       , testProperty "iterateN" prop_iterateN
       , testProperty "unfoldr" prop_unfoldr
       , testProperty "unfoldl" prop_unfoldl
       , testProperty "null" prop_null
       , testProperty "length" prop_length
       , testProperty "viewl" prop_viewl
       , testProperty "viewr" prop_viewr
       , testProperty "scanl" prop_scanl
       , testProperty "scanl1" prop_scanl1
       , testProperty "scanr" prop_scanr
       , testProperty "scanr1" prop_scanr1
       , testProperty "tails" prop_tails
       , testProperty "inits" prop_inits
       , testProperty "takeWhileL" prop_takeWhileL
       , testProperty "takeWhileR" prop_takeWhileR
       , testProperty "dropWhileL" prop_dropWhileL
       , testProperty "dropWhileR" prop_dropWhileR
       , testProperty "spanl" prop_spanl
       , testProperty "spanr" prop_spanr
       , testProperty "breakl" prop_breakl
       , testProperty "breakr" prop_breakr
       , testProperty "partition" prop_partition
       , testProperty "filter" prop_filter
       , testProperty "sort" prop_sort
       , testProperty "sortBy" prop_sortBy
       , testProperty "unstableSort" prop_unstableSort
       , testProperty "unstableSortBy" prop_unstableSortBy
       , testProperty "index" prop_index
       , testProperty "adjust" prop_adjust
       , testProperty "update" prop_update
       , testProperty "take" prop_take
       , testProperty "drop" prop_drop
       , testProperty "splitAt" prop_splitAt
       , testProperty "elemIndexL" prop_elemIndexL
       , testProperty "elemIndicesL" prop_elemIndicesL
       , testProperty "elemIndexR" prop_elemIndexR
       , testProperty "elemIndicesR" prop_elemIndicesR
       , testProperty "findIndexL" prop_findIndexL
       , testProperty "findIndicesL" prop_findIndicesL
       , testProperty "findIndexR" prop_findIndexR
       , testProperty "findIndicesR" prop_findIndicesR
       , testProperty "foldlWithIndex" prop_foldlWithIndex
       , testProperty "foldrWithIndex" prop_foldrWithIndex
       , testProperty "mapWithIndex" prop_mapWithIndex
       , testProperty "reverse" prop_reverse
       , testProperty "zip" prop_zip
       , testProperty "zipWith" prop_zipWith
       , testProperty "zip3" prop_zip3
       , testProperty "zipWith3" prop_zipWith3
       , testProperty "zip4" prop_zip4
       , testProperty "zipWith4" prop_zipWith4
       ] opts

  where
    opts = mempty { ropt_test_options = Just $ mempty { topt_maximum_generated_tests = Just 500
                                                      , topt_maximum_unsuitable_generated_tests = Just 500
                                                      }
                  }

------------------------------------------------------------------------
-- Arbitrary
------------------------------------------------------------------------

instance Arbitrary a => Arbitrary (Seq a) where
    arbitrary = Seq <$> arbitrary
    shrink (Seq x) = map Seq (shrink x)

instance Arbitrary a => Arbitrary (Elem a) where
    arbitrary = Elem <$> arbitrary

instance (Arbitrary a, Sized a) => Arbitrary (FingerTree a) where
    arbitrary = sized arb
      where
        arb :: (Arbitrary a, Sized a) => Int -> Gen (FingerTree a)
        arb 0 = return Empty
        arb 1 = Single <$> arbitrary
        arb n = deep <$> arbitrary <*> arb (n `div` 2) <*> arbitrary

    shrink (Deep _ (One a) Empty (One b)) = [Single a, Single b]
    shrink (Deep _ pr m sf) =
        [deep pr' m sf | pr' <- shrink pr] ++
        [deep pr m' sf | m' <- shrink m] ++
        [deep pr m sf' | sf' <- shrink sf]
    shrink (Single x) = map Single (shrink x)
    shrink Empty = []

instance (Arbitrary a, Sized a) => Arbitrary (Node a) where
    arbitrary = oneof [
        node2 <$> arbitrary <*> arbitrary,
        node3 <$> arbitrary <*> arbitrary <*> arbitrary]

    shrink (Node2 _ a b) =
        [node2 a' b | a' <- shrink a] ++
        [node2 a b' | b' <- shrink b]
    shrink (Node3 _ a b c) =
        [node2 a b, node2 a c, node2 b c] ++
        [node3 a' b c | a' <- shrink a] ++
        [node3 a b' c | b' <- shrink b] ++
        [node3 a b c' | c' <- shrink c]

instance Arbitrary a => Arbitrary (Digit a) where
    arbitrary = oneof [
        One <$> arbitrary,
        Two <$> arbitrary <*> arbitrary,
        Three <$> arbitrary <*> arbitrary <*> arbitrary,
        Four <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary]

    shrink (One a) = map One (shrink a)
    shrink (Two a b) = [One a, One b]
    shrink (Three a b c) = [Two a b, Two a c, Two b c]
    shrink (Four a b c d) = [Three a b c, Three a b d, Three a c d, Three b c d]

------------------------------------------------------------------------
-- Valid trees
------------------------------------------------------------------------

class Valid a where
    valid :: a -> Bool

instance Valid (Elem a) where
    valid _ = True

instance Valid (Seq a) where
    valid (Seq xs) = valid xs

instance (Sized a, Valid a) => Valid (FingerTree a) where
    valid Empty = True
    valid (Single x) = valid x
    valid (Deep s pr m sf) =
        s == size pr + size m + size sf && valid pr && valid m && valid sf

instance (Sized a, Valid a) => Valid (Node a) where
    valid node = size node == sum (fmap size node) && all valid node

instance Valid a => Valid (Digit a) where
    valid = all valid

{--------------------------------------------------------------------
  The general plan is to compare each function with a list equivalent.
  Each operation should produce a valid tree representing the same
  sequence as produced by its list counterpart on corresponding inputs.
  (The list versions are often lazier, but these properties ignore
  strictness.)
--------------------------------------------------------------------}

-- utilities for partial conversions

infix 4 ~=

(~=) :: Eq a => Maybe a -> a -> Bool
(~=) = maybe (const False) (==)

-- Partial conversion of an output sequence to a list.
toList' :: Seq a -> Maybe [a]
toList' xs
  | valid xs = Just (toList xs)
  | otherwise = Nothing

toListList' :: Seq (Seq a) -> Maybe [[a]]
toListList' xss = toList' xss >>= mapM toList'

toListPair' :: (Seq a, Seq b) -> Maybe ([a], [b])
toListPair' (xs, ys) = (,) <$> toList' xs <*> toList' ys

-- instances

prop_fmap :: Seq Int -> Bool
prop_fmap xs =
    toList' (fmap f xs) ~= map f (toList xs)
  where f = (+100)

prop_constmap :: A -> Seq A -> Bool
prop_constmap x xs =
    toList' (x <$ xs) ~= map (const x) (toList xs)

prop_foldr :: Seq A -> Bool
prop_foldr xs =
    foldr f z xs == Prelude.foldr f z (toList xs)
  where
    f = (:)
    z = []

prop_foldr1 :: Seq Int -> Property
prop_foldr1 xs =
    not (null xs) ==> foldr1 f xs == Data.List.foldr1 f (toList xs)
  where f = (-)

prop_foldl :: Seq A -> Bool
prop_foldl xs =
    foldl f z xs == Prelude.foldl f z (toList xs)
  where
    f = flip (:)
    z = []

prop_foldl1 :: Seq Int -> Property
prop_foldl1 xs =
    not (null xs) ==> foldl1 f xs == Data.List.foldl1 f (toList xs)
  where f = (-)

prop_equals :: Seq OrdA -> Seq OrdA -> Bool
prop_equals xs ys =
    (xs == ys) == (toList xs == toList ys)

prop_compare :: Seq OrdA -> Seq OrdA -> Bool
prop_compare xs ys =
    compare xs ys == compare (toList xs) (toList ys)

prop_mappend :: Seq A -> Seq A -> Bool
prop_mappend xs ys =
    toList' (mappend xs ys) ~= toList xs ++ toList ys

-- * Construction

{-
    toList' empty ~= []
-}

prop_singleton :: A -> Bool
prop_singleton x =
    toList' (singleton x) ~= [x]

prop_cons :: A -> Seq A -> Bool
prop_cons x xs =
    toList' (x <| xs) ~= x : toList xs

prop_snoc :: Seq A -> A -> Bool
prop_snoc xs x =
    toList' (xs |> x) ~= toList xs ++ [x]

prop_append :: Seq A -> Seq A -> Bool
prop_append xs ys =
    toList' (xs >< ys) ~= toList xs ++ toList ys

prop_fromList :: [A] -> Bool
prop_fromList xs =
    toList' (fromList xs) ~= xs

-- ** Repetition

prop_replicate :: NonNegative Int -> A -> Bool
prop_replicate (NonNegative m) x =
    toList' (replicate n x) ~= Prelude.replicate n x
  where n = m `mod` 10000

prop_replicateA :: NonNegative Int -> Bool
prop_replicateA (NonNegative m) =
    traverse toList' (replicateA n a) ~= sequenceA (Prelude.replicate n a)
  where
    n = m `mod` 10000
    a = Action 1 0 :: M Int

prop_replicateM :: NonNegative Int -> Bool
prop_replicateM (NonNegative m) =
    traverse toList' (replicateM n a) ~= sequence (Prelude.replicate n a)
  where
    n = m `mod` 10000
    a = Action 1 0 :: M Int

-- ** Iterative construction

prop_iterateN :: NonNegative Int -> Int -> Bool
prop_iterateN (NonNegative m) x =
    toList' (iterateN n f x) ~= Prelude.take n (Prelude.iterate f x)
  where
    n = m `mod` 10000
    f = (+1)

prop_unfoldr :: [A] -> Bool
prop_unfoldr z =
    toList' (unfoldr f z) ~= Data.List.unfoldr f z
  where
    f [] = Nothing
    f (x:xs) = Just (x, xs)

prop_unfoldl :: [A] -> Bool
prop_unfoldl z =
    toList' (unfoldl f z) ~= Data.List.reverse (Data.List.unfoldr (fmap swap . f) z)
  where
    f [] = Nothing
    f (x:xs) = Just (xs, x)
    swap (x,y) = (y,x)

-- * Deconstruction

-- ** Queries

prop_null :: Seq A -> Bool
prop_null xs =
    null xs == Prelude.null (toList xs)

prop_length :: Seq A -> Bool
prop_length xs =
    length xs == Prelude.length (toList xs)

-- ** Views

prop_viewl :: Seq A -> Bool
prop_viewl xs =
    case viewl xs of
    EmptyL ->   Prelude.null (toList xs)
    x :< xs' -> valid xs' && toList xs == x : toList xs'

prop_viewr :: Seq A -> Bool
prop_viewr xs =
    case viewr xs of
    EmptyR ->   Prelude.null (toList xs)
    xs' :> x -> valid xs' && toList xs == toList xs' ++ [x]

-- * Scans

prop_scanl :: [A] -> Seq A -> Bool
prop_scanl z xs =
    toList' (scanl f z xs) ~= Data.List.scanl f z (toList xs)
  where f = flip (:)

prop_scanl1 :: Seq Int -> Property
prop_scanl1 xs =
    not (null xs) ==> toList' (scanl1 f xs) ~= Data.List.scanl1 f (toList xs)
  where f = (-)

prop_scanr :: [A] -> Seq A -> Bool
prop_scanr z xs =
    toList' (scanr f z xs) ~= Data.List.scanr f z (toList xs)
  where f = (:)

prop_scanr1 :: Seq Int -> Property
prop_scanr1 xs =
    not (null xs) ==> toList' (scanr1 f xs) ~= Data.List.scanr1 f (toList xs)
  where f = (-)

-- * Sublists

prop_tails :: Seq A -> Bool
prop_tails xs =
    toListList' (tails xs) ~= Data.List.tails (toList xs)

prop_inits :: Seq A -> Bool
prop_inits xs =
    toListList' (inits xs) ~= Data.List.inits (toList xs)

-- ** Sequential searches
-- We use predicates with varying density.

prop_takeWhileL :: Positive Int -> Seq Int -> Bool
prop_takeWhileL (Positive n) xs =
    toList' (takeWhileL p xs) ~= Prelude.takeWhile p (toList xs)
  where p x = x `mod` n == 0

prop_takeWhileR :: Positive Int -> Seq Int -> Bool
prop_takeWhileR (Positive n) xs =
    toList' (takeWhileR p xs) ~= Prelude.reverse (Prelude.takeWhile p (Prelude.reverse (toList xs)))
  where p x = x `mod` n == 0

prop_dropWhileL :: Positive Int -> Seq Int -> Bool
prop_dropWhileL (Positive n) xs =
    toList' (dropWhileL p xs) ~= Prelude.dropWhile p (toList xs)
  where p x = x `mod` n == 0

prop_dropWhileR :: Positive Int -> Seq Int -> Bool
prop_dropWhileR (Positive n) xs =
    toList' (dropWhileR p xs) ~= Prelude.reverse (Prelude.dropWhile p (Prelude.reverse (toList xs)))
  where p x = x `mod` n == 0

prop_spanl :: Positive Int -> Seq Int -> Bool
prop_spanl (Positive n) xs =
    toListPair' (spanl p xs) ~= Data.List.span p (toList xs)
  where p x = x `mod` n == 0

prop_spanr :: Positive Int -> Seq Int -> Bool
prop_spanr (Positive n) xs =
    toListPair' (spanr p xs) ~= (Prelude.reverse *** Prelude.reverse) (Data.List.span p (Prelude.reverse (toList xs)))
  where p x = x `mod` n == 0

prop_breakl :: Positive Int -> Seq Int -> Bool
prop_breakl (Positive n) xs =
    toListPair' (breakl p xs) ~= Data.List.break p (toList xs)
  where p x = x `mod` n == 0

prop_breakr :: Positive Int -> Seq Int -> Bool
prop_breakr (Positive n) xs =
    toListPair' (breakr p xs) ~= (Prelude.reverse *** Prelude.reverse) (Data.List.break p (Prelude.reverse (toList xs)))
  where p x = x `mod` n == 0

prop_partition :: Positive Int -> Seq Int -> Bool
prop_partition (Positive n) xs =
    toListPair' (partition p xs) ~= Data.List.partition p (toList xs)
  where p x = x `mod` n == 0

prop_filter :: Positive Int -> Seq Int -> Bool
prop_filter (Positive n) xs =
    toList' (filter p xs) ~= Prelude.filter p (toList xs)
  where p x = x `mod` n == 0

-- * Sorting

prop_sort :: Seq OrdA -> Bool
prop_sort xs =
    toList' (sort xs) ~= Data.List.sort (toList xs)

prop_sortBy :: Seq (OrdA, B) -> Bool
prop_sortBy xs =
    toList' (sortBy f xs) ~= Data.List.sortBy f (toList xs)
  where f (x1, _) (x2, _) = compare x1 x2

prop_unstableSort :: Seq OrdA -> Bool
prop_unstableSort xs =
    toList' (unstableSort xs) ~= Data.List.sort (toList xs)

prop_unstableSortBy :: Seq OrdA -> Bool
prop_unstableSortBy xs =
    toList' (unstableSortBy compare xs) ~= Data.List.sort (toList xs)

-- * Indexing

prop_index :: Seq A -> Property
prop_index xs =
    not (null xs) ==> forAll (choose (0, length xs-1)) $ \ i ->
    index xs i == toList xs !! i

prop_adjust :: Int -> Int -> Seq Int -> Bool
prop_adjust n i xs =
    toList' (adjust f i xs) ~= adjustList f i (toList xs)
  where f = (+n)

prop_update :: Int -> A -> Seq A -> Bool
prop_update i x xs =
    toList' (update i x xs) ~= adjustList (const x) i (toList xs)

prop_take :: Int -> Seq A -> Bool
prop_take n xs =
    toList' (take n xs) ~= Prelude.take n (toList xs)

prop_drop :: Int -> Seq A -> Bool
prop_drop n xs =
    toList' (drop n xs) ~= Prelude.drop n (toList xs)

prop_splitAt :: Int -> Seq A -> Bool
prop_splitAt n xs =
    toListPair' (splitAt n xs) ~= Prelude.splitAt n (toList xs)

adjustList :: (a -> a) -> Int -> [a] -> [a]
adjustList f i xs =
    [if j == i then f x else x | (j, x) <- Prelude.zip [0..] xs]

-- ** Indexing with predicates
-- The elem* tests have poor coverage, but for find* we use predicates
-- of varying density.

prop_elemIndexL :: A -> Seq A -> Bool
prop_elemIndexL x xs =
    elemIndexL x xs == Data.List.elemIndex x (toList xs)

prop_elemIndicesL :: A -> Seq A -> Bool
prop_elemIndicesL x xs =
    elemIndicesL x xs == Data.List.elemIndices x (toList xs)

prop_elemIndexR :: A -> Seq A -> Bool
prop_elemIndexR x xs =
    elemIndexR x xs == listToMaybe (Prelude.reverse (Data.List.elemIndices x (toList xs)))

prop_elemIndicesR :: A -> Seq A -> Bool
prop_elemIndicesR x xs =
    elemIndicesR x xs == Prelude.reverse (Data.List.elemIndices x (toList xs))

prop_findIndexL :: Positive Int -> Seq Int -> Bool
prop_findIndexL (Positive n) xs =
    findIndexL p xs == Data.List.findIndex p (toList xs)
  where p x = x `mod` n == 0

prop_findIndicesL :: Positive Int -> Seq Int -> Bool
prop_findIndicesL (Positive n) xs =
    findIndicesL p xs == Data.List.findIndices p (toList xs)
  where p x = x `mod` n == 0

prop_findIndexR :: Positive Int -> Seq Int -> Bool
prop_findIndexR (Positive n) xs =
    findIndexR p xs == listToMaybe (Prelude.reverse (Data.List.findIndices p (toList xs)))
  where p x = x `mod` n == 0

prop_findIndicesR :: Positive Int -> Seq Int -> Bool
prop_findIndicesR (Positive n) xs =
    findIndicesR p xs == Prelude.reverse (Data.List.findIndices p (toList xs))
  where p x = x `mod` n == 0

-- * Folds

prop_foldlWithIndex :: [(Int, A)] -> Seq A -> Bool
prop_foldlWithIndex z xs =
    foldlWithIndex f z xs == Data.List.foldl (uncurry . f) z (Data.List.zip [0..] (toList xs))
  where f ys n y = (n,y):ys

prop_foldrWithIndex :: [(Int, A)] -> Seq A -> Bool
prop_foldrWithIndex z xs =
    foldrWithIndex f z xs == Data.List.foldr (uncurry f) z (Data.List.zip [0..] (toList xs))
  where f n y ys = (n,y):ys

-- * Transformations

prop_mapWithIndex :: Seq A -> Bool
prop_mapWithIndex xs =
    toList' (mapWithIndex f xs) ~= map (uncurry f) (Data.List.zip [0..] (toList xs))
  where f = (,)

prop_reverse :: Seq A -> Bool
prop_reverse xs =
    toList' (reverse xs) ~= Prelude.reverse (toList xs)

-- ** Zips

prop_zip :: Seq A -> Seq B -> Bool
prop_zip xs ys =
    toList' (zip xs ys) ~= Prelude.zip (toList xs) (toList ys)

prop_zipWith :: Seq A -> Seq B -> Bool
prop_zipWith xs ys =
    toList' (zipWith f xs ys) ~= Prelude.zipWith f (toList xs) (toList ys)
  where f = (,)

prop_zip3 :: Seq A -> Seq B -> Seq C -> Bool
prop_zip3 xs ys zs =
    toList' (zip3 xs ys zs) ~= Prelude.zip3 (toList xs) (toList ys) (toList zs)

prop_zipWith3 :: Seq A -> Seq B -> Seq C -> Bool
prop_zipWith3 xs ys zs =
    toList' (zipWith3 f xs ys zs) ~= Prelude.zipWith3 f (toList xs) (toList ys) (toList zs)
  where f = (,,)

prop_zip4 :: Seq A -> Seq B -> Seq C -> Seq Int -> Bool
prop_zip4 xs ys zs ts =
    toList' (zip4 xs ys zs ts) ~= Data.List.zip4 (toList xs) (toList ys) (toList zs) (toList ts)

prop_zipWith4 :: Seq A -> Seq B -> Seq C -> Seq Int -> Bool
prop_zipWith4 xs ys zs ts =
    toList' (zipWith4 f xs ys zs ts) ~= Data.List.zipWith4 f (toList xs) (toList ys) (toList zs) (toList ts)
  where f = (,,,)

-- Simple test monad

data M a = Action Int a
    deriving (Eq, Show)

instance Functor M where
    fmap f (Action n x) = Action n (f x)

instance Applicative M where
    pure x = Action 0 x
    Action m f <*> Action n x = Action (m+n) (f x)

instance Monad M where
    return x = Action 0 x
    Action m x >>= f = let Action n y = f x in Action (m+n) y

instance Foldable M where
    foldMap f (Action _ x) = f x

instance Traversable M where
    traverse f (Action n x) = Action n <$> f x
