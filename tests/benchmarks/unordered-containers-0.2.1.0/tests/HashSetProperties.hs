 {-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | Tests for the 'Data.HashSet' module.  We test functions by
-- comparing them to a simpler model, a list.

module Main (main) where

import qualified Data.Foldable as Foldable
import Data.Hashable (Hashable(hash))
import qualified Data.List as L
import qualified Data.HashSet as S
import qualified Data.Set as Set
import Test.QuickCheck (Arbitrary)
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)

-- Key type that generates more hash collisions.
newtype Key = K { unK :: Int }
            deriving (Arbitrary, Enum, Eq, Integral, Num, Ord, Show, Real)

instance Hashable Key where
    hash k = hash (unK k) `mod` 20

------------------------------------------------------------------------
-- * Properties

------------------------------------------------------------------------
-- ** Instances

pEq :: [Key] -> [Key] -> Bool
pEq xs = (Set.fromList xs ==) `eq` (S.fromList xs ==)

pNeq :: [Key] -> [Key] -> Bool
pNeq xs = (Set.fromList xs /=) `eq` (S.fromList xs /=)

pFoldable :: [Int] -> Bool
pFoldable = (L.sort . Foldable.foldr (:) []) `eq`
            (L.sort . Foldable.foldr (:) [])

------------------------------------------------------------------------
-- ** Basic interface

pSize :: [Key] -> Bool
pSize = Set.size `eq` S.size

pMember :: Key -> [Key] -> Bool
pMember k = Set.member k `eq` S.member k

pInsert :: Key -> [Key] -> Bool
pInsert a = Set.insert a `eq_` S.insert a

pDelete :: Key -> [Key] -> Bool
pDelete a = Set.delete a `eq_` S.delete a

------------------------------------------------------------------------
-- ** Combine

pUnion :: [Key] -> [Key] -> Bool
pUnion xs ys = Set.union (Set.fromList xs) `eq_`
               S.union (S.fromList xs) $ ys

------------------------------------------------------------------------
-- ** Transformations

pMap :: [Key] -> Bool
pMap = Set.map (+ 1) `eq_` S.map (+ 1)

------------------------------------------------------------------------
-- ** Folds

pFoldr :: [Int] -> Bool
pFoldr = (L.sort . Set.foldr (:) []) `eq`
         (L.sort . S.foldr (:) [])

pFoldl' :: Int -> [Int] -> Bool
pFoldl' z0 = Set.foldl' (+) z0 `eq` S.foldl' (+) z0

------------------------------------------------------------------------
-- ** Filter

pFilter :: [Key] -> Bool
pFilter = Set.filter odd `eq_` S.filter odd

------------------------------------------------------------------------
-- ** Conversions

pToList :: [Key] -> Bool
pToList = Set.toAscList `eq` toAscList

------------------------------------------------------------------------
-- * Test list

tests :: [Test]
tests =
    [
    -- Instances
      testGroup "instances"
      [ testProperty "==" pEq
      , testProperty "/=" pNeq
      , testProperty "Foldable" pFoldable
      ]
    -- Basic interface
    , testGroup "basic interface"
      [ testProperty "size" pSize
      , testProperty "member" pMember
      , testProperty "insert" pInsert
      , testProperty "delete" pDelete
      ]
    -- Combine
    , testProperty "union" pUnion
    -- Transformations
    , testProperty "map" pMap
    -- Folds
    , testGroup "folds"
      [ testProperty "foldr" pFoldr
      , testProperty "foldl'" pFoldl'
      ]
    -- Filter
    , testGroup "filter"
      [ testProperty "filter" pFilter
      ]
    -- Conversions
    , testGroup "conversions"
      [ testProperty "toList" pToList
      ]
    ]

------------------------------------------------------------------------
-- * Model

-- Invariant: the list is sorted in ascending order, by key.
type Model a = Set.Set a

-- | Check that a function operating on a 'HashMap' is equivalent to
-- one operating on a 'Model'.
eq :: (Eq a, Hashable a, Ord a, Eq b)
   => (Model a -> b)      -- ^ Function that modifies a 'Model' in the same
                          -- way
   -> (S.HashSet a -> b)  -- ^ Function that modified a 'HashSet'
   -> [a]                 -- ^ Initial content of the 'HashSet' and 'Model'
   -> Bool                -- ^ True if the functions are equivalent
eq f g xs = g (S.fromList xs) == f (Set.fromList xs)

eq_ :: (Eq a, Hashable a, Ord a)
    => (Model a -> Model a)          -- ^ Function that modifies a 'Model'
    -> (S.HashSet a -> S.HashSet a)  -- ^ Function that modified a
                                     -- 'HashSet' in the same way
    -> [a]                           -- ^ Initial content of the 'HashSet'
                                     -- and 'Model'
    -> Bool                          -- ^ True if the functions are
                                     -- equivalent
eq_ f g = (Set.toAscList . f) `eq` (toAscList . g)

------------------------------------------------------------------------
-- * Test harness

main :: IO ()
main = defaultMain tests

------------------------------------------------------------------------
-- * Helpers

toAscList :: Ord a => S.HashSet a -> [a]
toAscList = L.sort . S.toList
