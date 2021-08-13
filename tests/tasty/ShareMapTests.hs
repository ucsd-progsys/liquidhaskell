{-# LANGUAGE FlexibleInstances #-}

module ShareMapTests where

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.List (foldl', nub)
import qualified Data.ShareMap as ShareMap
import qualified ShareMapReference as Reference
import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit

-- | Compare Data.ShareMap against a reference implementation
tests :: TestTree
tests =
  localOption (QuickCheckMaxSize 50) $
  localOption (QuickCheckTests 500) $
  testGroup "Data.ShareMap"
    [ testProperty "behaves as ShareMapReference" $ \xs ->
        let m1 :: HashMap Int [Int]
            m1 = Reference.toHashMap $
                  interpretSteps
                    (Reference.insertWith (++))
                    (Reference.mergeKeysWith (++))
                    Reference.empty
                    xs
            m2 = ShareMap.toHashMap $
                  interpretSteps
                    (ShareMap.insertWith (++))
                    (ShareMap.mergeKeysWith (++))
                    ShareMap.empty
                    xs
         in m1 === m2
    ]

-- | The steps to use to generate a ShareMap
data ShareMapStep k v
  = Insert k v
  | MergeKeys k k
  deriving Show

-- | Run a sequence of steps to produce some sharemap
interpretSteps
  :: (k -> v -> a -> a)
  -> (k -> k -> a -> a)
  -> a
  -> [ShareMapStep k v]
  -> a
interpretSteps f g = foldl' $ \a x -> case x of
  Insert k v -> f k v a
  MergeKeys k1 k2 -> g k1 k2 a

instance Arbitrary (ShareMapStep Int [Int]) where
  arbitrary = do
    n <- getSize
    let sz = 8
    resize (min n sz) $ frequency
      [ ( 1
        , Insert
            <$> choose (1, sz)
            <*> (nub <$> listOf (choose (1, sz)))
        )
      , ( 1
        , MergeKeys
            <$> choose (1, sz)
            <*> choose (1, sz)
        )
      ]
  shrink s = case s of
    Insert k v -> Insert k <$> shrink v
    _ -> []
