import qualified Data.IntSet as IntSet
import Data.List (nub,sort)
import qualified Data.List as List
import Data.Monoid (mempty)
import Data.Set
import Prelude hiding (lookup, null, map, filter, foldr, foldl)
import Test.Framework
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2
import Test.HUnit hiding (Test, Testable)
import Test.QuickCheck

main :: IO ()
main = defaultMainWithOpts [ testCase "lookupLT" test_lookupLT
                           , testCase "lookupGT" test_lookupGT
                           , testCase "lookupLE" test_lookupLE
                           , testCase "lookupGE" test_lookupGE
                           , testProperty "prop_Valid" prop_Valid
                           , testProperty "prop_Single" prop_Single
                           , testProperty "prop_Member" prop_Member
                           , testProperty "prop_NotMember" prop_NotMember
                           , testProperty "prop_LookupLT" prop_LookupLT
                           , testProperty "prop_LookupGT" prop_LookupGT
                           , testProperty "prop_LookupLE" prop_LookupLE
                           , testProperty "prop_LookupGE" prop_LookupGE
                           , testProperty "prop_InsertValid" prop_InsertValid
                           , testProperty "prop_InsertDelete" prop_InsertDelete
                           , testProperty "prop_DeleteValid" prop_DeleteValid
                           , testProperty "prop_Join" prop_Join
                           , testProperty "prop_Merge" prop_Merge
                           , testProperty "prop_UnionValid" prop_UnionValid
                           , testProperty "prop_UnionInsert" prop_UnionInsert
                           , testProperty "prop_UnionAssoc" prop_UnionAssoc
                           , testProperty "prop_UnionComm" prop_UnionComm
                           , testProperty "prop_DiffValid" prop_DiffValid
                           , testProperty "prop_Diff" prop_Diff
                           , testProperty "prop_IntValid" prop_IntValid
                           , testProperty "prop_Int" prop_Int
                           , testProperty "prop_Ordered" prop_Ordered
                           , testProperty "prop_List" prop_List
                           , testProperty "prop_DescList" prop_DescList
                           , testProperty "prop_AscDescList" prop_AscDescList
                           , testProperty "prop_fromList" prop_fromList
                           , testProperty "prop_isProperSubsetOf" prop_isProperSubsetOf
                           , testProperty "prop_isProperSubsetOf2" prop_isProperSubsetOf2
                           , testProperty "prop_isSubsetOf" prop_isSubsetOf
                           , testProperty "prop_isSubsetOf2" prop_isSubsetOf2
                           , testProperty "prop_size" prop_size
                           , testProperty "prop_findMax" prop_findMax
                           , testProperty "prop_findMin" prop_findMin
                           , testProperty "prop_ord" prop_ord
                           , testProperty "prop_readShow" prop_readShow
                           , testProperty "prop_foldR" prop_foldR
                           , testProperty "prop_foldR'" prop_foldR'
                           , testProperty "prop_foldL" prop_foldL
                           , testProperty "prop_foldL'" prop_foldL'
                           , testProperty "prop_map" prop_map
                           , testProperty "prop_maxView" prop_maxView
                           , testProperty "prop_minView" prop_minView
                           , testProperty "prop_split" prop_split
                           , testProperty "prop_splitMember" prop_splitMember
                           , testProperty "prop_partition" prop_partition
                           , testProperty "prop_filter" prop_filter
                           ] opts
  where
    opts = mempty { ropt_test_options = Just $ mempty { topt_maximum_generated_tests = Just 500
                                                      , topt_maximum_unsuitable_generated_tests = Just 500
                                                      }
                  }

----------------------------------------------------------------
-- Unit tests
----------------------------------------------------------------

test_lookupLT :: Assertion
test_lookupLT = do
    lookupLT 3 (fromList [3, 5]) @?= Nothing
    lookupLT 5 (fromList [3, 5]) @?= Just 3

test_lookupGT :: Assertion
test_lookupGT = do
   lookupGT 4 (fromList [3, 5]) @?= Just 5
   lookupGT 5 (fromList [3, 5]) @?= Nothing

test_lookupLE :: Assertion
test_lookupLE = do
   lookupLE 2 (fromList [3, 5]) @?= Nothing
   lookupLE 4 (fromList [3, 5]) @?= Just 3
   lookupLE 5 (fromList [3, 5]) @?= Just 5

test_lookupGE :: Assertion
test_lookupGE = do
   lookupGE 3 (fromList [3, 5]) @?= Just 3
   lookupGE 4 (fromList [3, 5]) @?= Just 5
   lookupGE 6 (fromList [3, 5]) @?= Nothing

{--------------------------------------------------------------------
  Arbitrary, reasonably balanced trees
--------------------------------------------------------------------}
instance (Enum a) => Arbitrary (Set a) where
    arbitrary = sized (arbtree 0 maxkey)
      where maxkey = 10000

            arbtree :: (Enum a) => Int -> Int -> Int -> Gen (Set a)
            arbtree lo hi n = do t <- gentree lo hi n
                                 if balanced t then return t else arbtree lo hi n
              where gentree lo hi n
                      | n <= 0    = return Tip
                      | lo >= hi  = return Tip
                      | otherwise = do  i  <- choose (lo,hi)
                                        m  <- choose (1,70)
                                        let (ml,mr) | m==(1::Int) = (1,2)
                                                    | m==2        = (2,1)
                                                    | m==3        = (1,1)
                                                    | otherwise   = (2,2)
                                        l  <- gentree lo (i-1) (n `div` ml)
                                        r  <- gentree (i+1) hi (n `div` mr)
                                        return (bin (toEnum i) l r)

{--------------------------------------------------------------------
  Valid tree's
--------------------------------------------------------------------}
forValid :: (Enum a,Show a,Testable b) => (Set a -> b) -> Property
forValid f = forAll arbitrary $ \t ->
--    classify (balanced t) "balanced" $
    classify (size t == 0) "empty" $
    classify (size t > 0  && size t <= 10) "small" $
    classify (size t > 10 && size t <= 64) "medium" $
    classify (size t > 64) "large" $
    balanced t ==> f t

forValidUnitTree :: Testable a => (Set Int -> a) -> Property
forValidUnitTree f = forValid f

prop_Valid :: Property
prop_Valid = forValidUnitTree $ \t -> valid t

{--------------------------------------------------------------------
  Single, Member, Insert, Delete
--------------------------------------------------------------------}
prop_Single :: Int -> Bool
prop_Single x = (insert x empty == singleton x)

prop_Member :: [Int] -> Int -> Bool
prop_Member xs n =
  let m  = fromList xs
  in all (\k -> k `member` m == (k `elem` xs)) (n : xs)

prop_NotMember :: [Int] -> Int -> Bool
prop_NotMember xs n =
  let m  = fromList xs
  in all (\k -> k `notMember` m == (k `notElem` xs)) (n : xs)

test_LookupSomething :: (Int -> Set Int -> Maybe Int) -> (Int -> Int -> Bool) -> [Int] -> Bool
test_LookupSomething lookup' cmp xs =
  let odd_sorted_xs = filter_odd $ nub $ sort xs
      t = fromList odd_sorted_xs
      test x = case List.filter (`cmp` x) odd_sorted_xs of
                 []             -> lookup' x t == Nothing
                 cs | 0 `cmp` 1 -> lookup' x t == Just (last cs) -- we want largest such element
                    | otherwise -> lookup' x t == Just (head cs) -- we want smallest such element
  in all test xs

  where filter_odd [] = []
        filter_odd [_] = []
        filter_odd (_ : o : xs) = o : filter_odd xs

prop_LookupLT :: [Int] -> Bool
prop_LookupLT = test_LookupSomething lookupLT (<)

prop_LookupGT :: [Int] -> Bool
prop_LookupGT = test_LookupSomething lookupGT (>)

prop_LookupLE :: [Int] -> Bool
prop_LookupLE = test_LookupSomething lookupLE (<=)

prop_LookupGE :: [Int] -> Bool
prop_LookupGE = test_LookupSomething lookupGE (>=)

prop_InsertValid :: Int -> Property
prop_InsertValid k = forValidUnitTree $ \t -> valid (insert k t)

prop_InsertDelete :: Int -> Set Int -> Property
prop_InsertDelete k t = not (member k t) ==> delete k (insert k t) == t

prop_DeleteValid :: Int -> Property
prop_DeleteValid k = forValidUnitTree $ \t -> valid (delete k (insert k t))

{--------------------------------------------------------------------
  Balance
--------------------------------------------------------------------}
prop_Join :: Int -> Property
prop_Join x = forValidUnitTree $ \t ->
    let (l,r) = split x t
    in valid (join x l r)

prop_Merge :: Int -> Property
prop_Merge x = forValidUnitTree $ \t ->
    let (l,r) = split x t
    in valid (merge l r)

{--------------------------------------------------------------------
  Union
--------------------------------------------------------------------}
prop_UnionValid :: Property
prop_UnionValid
  = forValidUnitTree $ \t1 ->
    forValidUnitTree $ \t2 ->
    valid (union t1 t2)

prop_UnionInsert :: Int -> Set Int -> Bool
prop_UnionInsert x t = union t (singleton x) == insert x t

prop_UnionAssoc :: Set Int -> Set Int -> Set Int -> Bool
prop_UnionAssoc t1 t2 t3 = union t1 (union t2 t3) == union (union t1 t2) t3

prop_UnionComm :: Set Int -> Set Int -> Bool
prop_UnionComm t1 t2 = (union t1 t2 == union t2 t1)

prop_DiffValid :: Property
prop_DiffValid = forValidUnitTree $ \t1 ->
    forValidUnitTree $ \t2 ->
    valid (difference t1 t2)

prop_Diff :: [Int] -> [Int] -> Bool
prop_Diff xs ys = toAscList (difference (fromList xs) (fromList ys))
                  == List.sort ((List.\\) (nub xs)  (nub ys))

prop_IntValid :: Property
prop_IntValid = forValidUnitTree $ \t1 ->
    forValidUnitTree $ \t2 ->
    valid (intersection t1 t2)

prop_Int :: [Int] -> [Int] -> Bool
prop_Int xs ys = toAscList (intersection (fromList xs) (fromList ys))
                 == List.sort (nub ((List.intersect) (xs)  (ys)))

{--------------------------------------------------------------------
  Lists
--------------------------------------------------------------------}
prop_Ordered :: Property
prop_Ordered = forAll (choose (5,100)) $ \n ->
    let xs = [0..n::Int]
    in fromAscList xs == fromList xs

prop_List :: [Int] -> Bool
prop_List xs = (sort (nub xs) == toList (fromList xs))

prop_DescList :: [Int] -> Bool
prop_DescList xs = (reverse (sort (nub xs)) == toDescList (fromList xs))

prop_AscDescList :: [Int] -> Bool
prop_AscDescList xs = toAscList s == reverse (toDescList s)
  where s = fromList xs

prop_fromList :: [Int] -> Bool
prop_fromList xs
  = case fromList xs of
      t -> t == fromAscList sort_xs &&
           t == fromDistinctAscList nub_sort_xs &&
           t == List.foldr insert empty xs
  where sort_xs = sort xs
        nub_sort_xs = List.map List.head $ List.group sort_xs

{--------------------------------------------------------------------
  Set operations are like IntSet operations
--------------------------------------------------------------------}
toIntSet :: Set Int -> IntSet.IntSet
toIntSet = IntSet.fromList . toList

-- Check that Set Int.isProperSubsetOf is the same as Set.isProperSubsetOf.
prop_isProperSubsetOf :: Set Int -> Set Int -> Bool
prop_isProperSubsetOf a b = isProperSubsetOf a b == IntSet.isProperSubsetOf (toIntSet a) (toIntSet b)

-- In the above test, isProperSubsetOf almost always returns False (since a
-- random set is almost never a subset of another random set).  So this second
-- test checks the True case.
prop_isProperSubsetOf2 :: Set Int -> Set Int -> Bool
prop_isProperSubsetOf2 a b = isProperSubsetOf a c == (a /= c) where
  c = union a b

prop_isSubsetOf :: Set Int -> Set Int -> Bool
prop_isSubsetOf a b = isSubsetOf a b == IntSet.isSubsetOf (toIntSet a) (toIntSet b)

prop_isSubsetOf2 :: Set Int -> Set Int -> Bool
prop_isSubsetOf2 a b = isSubsetOf a (union a b)

prop_size :: Set Int -> Bool
prop_size s = size s == List.length (toList s)

prop_findMax :: Set Int -> Property
prop_findMax s = not (null s) ==> findMax s == maximum (toList s)

prop_findMin :: Set Int -> Property
prop_findMin s = not (null s) ==> findMin s == minimum (toList s)

prop_ord :: Set Int -> Set Int -> Bool
prop_ord s1 s2 = s1 `compare` s2 == toList s1 `compare` toList s2

prop_readShow :: Set Int -> Bool
prop_readShow s = s == read (show s)

prop_foldR :: Set Int -> Bool
prop_foldR s = foldr (:) [] s == toList s

prop_foldR' :: Set Int -> Bool
prop_foldR' s = foldr' (:) [] s == toList s

prop_foldL :: Set Int -> Bool
prop_foldL s = foldl (flip (:)) [] s == List.foldl (flip (:)) [] (toList s)

prop_foldL' :: Set Int -> Bool
prop_foldL' s = foldl' (flip (:)) [] s == List.foldl' (flip (:)) [] (toList s)

prop_map :: Set Int -> Bool
prop_map s = map id s == s

prop_maxView :: Set Int -> Bool
prop_maxView s = case maxView s of
    Nothing -> null s
    Just (m,s') -> m == maximum (toList s) && s == insert m s' && m `notMember` s'

prop_minView :: Set Int -> Bool
prop_minView s = case minView s of
    Nothing -> null s
    Just (m,s') -> m == minimum (toList s) && s == insert m s' && m `notMember` s'

prop_split :: Set Int -> Int -> Bool
prop_split s i = case split i s of
    (s1,s2) -> all (<i) (toList s1) && all (>i) (toList s2) && i `delete` s == union s1 s2

prop_splitMember :: Set Int -> Int -> Bool
prop_splitMember s i = case splitMember i s of
    (s1,t,s2) -> all (<i) (toList s1) && all (>i) (toList s2) && t == i `member` s && i `delete` s == union s1 s2

prop_partition :: Set Int -> Int -> Bool
prop_partition s i = case partition odd s of
    (s1,s2) -> all odd (toList s1) && all even (toList s2) && s == s1 `union` s2

prop_filter :: Set Int -> Int -> Bool
prop_filter s i = partition odd s == (filter odd s, filter even s)
