 {-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}

-- | Tests for the 'Data.HashMap.Lazy' module.  We test functions by
-- comparing them to a simpler model, an association list.

module Main (main) where

import qualified Data.Foldable as Foldable
import Data.Function (on)
import Data.Hashable (Hashable(hash))
import qualified Data.List as L
#if defined(STRICT)
import qualified Data.HashMap.Strict as HM
#else
import qualified Data.HashMap.Lazy as HM
#endif
import qualified Data.Map as M
import Test.QuickCheck (Arbitrary, Property, (==>))
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)

-- Key type that generates more hash collisions.
newtype Key = K { unK :: Int }
            deriving (Arbitrary, Eq, Ord, Show)

instance Hashable Key where
    hash k = hash (unK k) `mod` 20

------------------------------------------------------------------------
-- * Properties

------------------------------------------------------------------------
-- ** Instances

pEq :: [(Key, Int)] -> [(Key, Int)] -> Bool
pEq xs = (M.fromList xs ==) `eq` (HM.fromList xs ==)

pNeq :: [(Key, Int)] -> [(Key, Int)] -> Bool
pNeq xs = (M.fromList xs /=) `eq` (HM.fromList xs /=)

pFunctor :: [(Key, Int)] -> Bool
pFunctor = fmap (+ 1) `eq_` fmap (+ 1)

pFoldable :: [(Int, Int)] -> Bool
pFoldable = (L.sort . Foldable.foldr (:) []) `eq`
            (L.sort . Foldable.foldr (:) [])

------------------------------------------------------------------------
-- ** Basic interface

pSize :: [(Key, Int)] -> Bool
pSize = M.size `eq` HM.size

pMember :: Key -> [(Key, Int)] -> Bool
pMember k = M.member k `eq` HM.member k

pLookup :: Key -> [(Key, Int)] -> Bool
pLookup k = M.lookup k `eq` HM.lookup k

pInsert :: Key -> Int -> [(Key, Int)] -> Bool
pInsert k v = M.insert k v `eq_` HM.insert k v

pDelete :: Key -> [(Key, Int)] -> Bool
pDelete k = M.delete k `eq_` HM.delete k

newtype AlwaysCollide = AC Int
    deriving (Arbitrary, Eq, Ord, Show)

instance Hashable AlwaysCollide where
    hash _ = 1

-- White-box test that tests the case of deleting one of two keys from
-- a map, where the keys' hash values collide.
pDeleteCollision :: AlwaysCollide -> AlwaysCollide -> Bool -> Property
pDeleteCollision k1 k2 keepFst = k1 /= k2 ==> HM.member toKeep $ HM.delete toDelete $
                                 HM.fromList [(k1, 1 :: Int), (k2, 2)]
  where
    (toDelete, toKeep)
        | keepFst   = (k2, k1)
        | otherwise = (k1, k2)

-- White-box test that tests the case of deleting one of many keys
-- from a map, where the keys' hash values collide.
pDeleteCollisionMany :: AlwaysCollide -> [(AlwaysCollide, Int)] -> Bool
pDeleteCollisionMany k kvs = not $ (HM.member k) $ HM.delete k $
                             HM.fromList ((k, 1):kvs)

pInsertWith :: Key -> [(Key, Int)] -> Bool
pInsertWith k = M.insertWith (+) k 1 `eq_` HM.insertWith (+) k 1

pAdjust :: Key -> [(Key, Int)] -> Bool
pAdjust k = M.adjust succ k `eq_` HM.adjust succ k

------------------------------------------------------------------------
-- ** Combine

pUnion :: [(Key, Int)] -> [(Key, Int)] -> Bool
pUnion xs ys = M.union (M.fromList xs) `eq_` HM.union (HM.fromList xs) $ ys

pUnionWith :: [(Key, Int)] -> [(Key, Int)] -> Bool
pUnionWith xs ys = M.unionWith (-) (M.fromList xs) `eq_`
                   HM.unionWith (-) (HM.fromList xs) $ ys

pUnions :: [[(Key, Int)]] -> Bool
pUnions xss = M.toAscList (M.unions (map M.fromList xss)) ==
              toAscList (HM.unions (map HM.fromList xss))

------------------------------------------------------------------------
-- ** Transformations

pMap :: [(Key, Int)] -> Bool
pMap = M.map (+ 1) `eq_` HM.map (+ 1)

------------------------------------------------------------------------
-- ** Difference and intersection

pDifference :: [(Key, Int)] -> [(Key, Int)] -> Bool
pDifference xs ys = M.difference (M.fromList xs) `eq_`
                    HM.difference (HM.fromList xs) $ ys

pIntersection :: [(Key, Int)] -> [(Key, Int)] -> Bool
pIntersection xs ys = M.intersection (M.fromList xs) `eq_`
                      HM.intersection (HM.fromList xs) $ ys

------------------------------------------------------------------------
-- ** Folds

pFoldr :: [(Int, Int)] -> Bool
pFoldr = (L.sort . M.fold (:) []) `eq` (L.sort . HM.foldr (:) [])

pFoldrWithKey :: [(Int, Int)] -> Bool
pFoldrWithKey = (sortByKey . M.foldrWithKey f []) `eq`
                (sortByKey . HM.foldrWithKey f [])
  where f k v z = (k, v) : z

pFoldl' :: Int -> [(Int, Int)] -> Bool
pFoldl' z0 = M.foldlWithKey' (\ z _ v -> v + z) z0 `eq` HM.foldl' (+) z0

------------------------------------------------------------------------
-- ** Filter

pFilter :: [(Key, Int)] -> Bool
pFilter = M.filter odd `eq_` HM.filter odd

pFilterWithKey :: [(Key, Int)] -> Bool
pFilterWithKey = M.filterWithKey p `eq_` HM.filterWithKey p
  where p k v = odd (unK k + v)

------------------------------------------------------------------------
-- ** Conversions

-- 'eq_' already calls fromList.
pFromList :: [(Key, Int)] -> Bool
pFromList = id `eq_` id

pFromListWith :: [(Key, Int)] -> Bool
pFromListWith kvs = (M.toAscList $ M.fromListWith (+) kvs) ==
                    (toAscList $ HM.fromListWith (+) kvs)

pToList :: [(Key, Int)] -> Bool
pToList = M.toAscList `eq` toAscList

pElems :: [(Key, Int)] -> Bool
pElems = (L.sort . M.elems) `eq` (L.sort . HM.elems)

pKeys :: [(Key, Int)] -> Bool
pKeys = (L.sort . M.keys) `eq` (L.sort . HM.keys)

------------------------------------------------------------------------
-- * Test list

tests :: [Test]
tests =
    [
    -- Instances
      testGroup "instances"
      [ testProperty "==" pEq
      , testProperty "/=" pNeq
      , testProperty "Functor" pFunctor
      , testProperty "Foldable" pFoldable
      ]
    -- Basic interface
    , testGroup "basic interface"
      [ testProperty "size" pSize
      , testProperty "member" pMember
      , testProperty "lookup" pLookup
      , testProperty "insert" pInsert
      , testProperty "delete" pDelete
      , testProperty "deleteCollision" pDeleteCollision
      , testProperty "deleteCollisionMany" pDeleteCollisionMany
      , testProperty "insertWith" pInsertWith
      , testProperty "adjust" pAdjust
      ]
    -- Combine
    , testProperty "union" pUnion
    , testProperty "unionWith" pUnionWith
    , testProperty "unions" pUnions
    -- Transformations
    , testProperty "map" pMap
    -- Folds
    , testGroup "folds"
      [ testProperty "foldr" pFoldr
      , testProperty "foldrWithKey" pFoldrWithKey
      , testProperty "foldl'" pFoldl'
      ]
    , testGroup "difference and intersection"
      [ testProperty "difference" pDifference
      , testProperty "intersection" pIntersection
      ]
    -- Filter
    , testGroup "filter"
      [ testProperty "filter" pFilter
      , testProperty "filterWithKey" pFilterWithKey
      ]
    -- Conversions
    , testGroup "conversions"
      [ testProperty "elems" pElems
      , testProperty "keys" pKeys
      , testProperty "fromList" pFromList
      , testProperty "fromListWith" pFromListWith
      , testProperty "toList" pToList
      ]
    ]

------------------------------------------------------------------------
-- * Model

type Model k v = M.Map k v

-- | Check that a function operating on a 'HashMap' is equivalent to
-- one operating on a 'Model'.
eq :: (Eq a, Eq k, Hashable k, Ord k)
   => (Model k v -> a)       -- ^ Function that modifies a 'Model'
   -> (HM.HashMap k v -> a)  -- ^ Function that modified a 'HashMap' in the same
                             -- way
   -> [(k, v)]               -- ^ Initial content of the 'HashMap' and 'Model'
   -> Bool                   -- ^ True if the functions are equivalent
eq f g xs = g (HM.fromList xs) == f (M.fromList xs)

eq_ :: (Eq k, Eq v, Hashable k, Ord k)
    => (Model k v -> Model k v)            -- ^ Function that modifies a 'Model'
    -> (HM.HashMap k v -> HM.HashMap k v)  -- ^ Function that modified a
                                           -- 'HashMap' in the same way
    -> [(k, v)]                            -- ^ Initial content of the 'HashMap'
                                           -- and 'Model'
    -> Bool                                -- ^ True if the functions are
                                           -- equivalent
eq_ f g = (M.toAscList . f) `eq` (toAscList . g)

------------------------------------------------------------------------
-- * Test harness

main :: IO ()
main = defaultMain tests

------------------------------------------------------------------------
-- * Helpers

sortByKey :: Ord k => [(k, v)] -> [(k, v)]
sortByKey = L.sortBy (compare `on` fst)

toAscList :: Ord k => HM.HashMap k v -> [(k, v)]
toAscList = L.sortBy (compare `on` fst) . HM.toList
