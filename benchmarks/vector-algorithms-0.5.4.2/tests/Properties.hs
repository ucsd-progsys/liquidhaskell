{-# LANGUAGE RankNTypes, FlexibleContexts #-}

module Properties where

import Prelude

import Optimal

import Control.Monad
import Control.Monad.ST

import Data.List
import Data.Ord

import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.Vector.Mutable (MVector)
import qualified Data.Vector.Mutable as MV

import Data.Vector.Generic (modify)

import qualified Data.Vector.Generic.Mutable as G

import Data.Vector.Algorithms.Optimal (Comparison)
import Data.Vector.Algorithms.Radix (radix, passes, size)

import qualified Data.Map as M

import Test.QuickCheck

import Util

prop_sorted :: (Ord e) => Vector e -> Property
prop_sorted arr | V.length arr < 2 = property True
                | otherwise        = check (V.head arr) (V.tail arr)
 where
 check e arr | V.null arr = property True
             | otherwise  = e <= V.head arr .&. check (V.head arr) (V.tail arr)

prop_empty :: (Ord e) => (forall s. MV.MVector s e -> ST s ()) -> Property
prop_empty algo = prop_sorted (modify algo $ V.fromList [])

prop_fullsort :: (Ord e)
              => (forall s mv. G.MVector mv e => mv s e -> ST s ()) -> Vector e -> Property
prop_fullsort algo arr = prop_sorted $ modify algo arr

{-
prop_schwartzian :: (UA e, UA k, Ord k)
                 => (e -> k)
                 -> (forall e s. (UA e) => (e -> e -> Ordering) -> MUArr e s -> ST s ())
                 -> UArr e -> Property
prop_schwartzian f algo arr
  | lengthU arr < 2 = property True
  | otherwise       = let srt = modify (algo `usingKeys` f) arr
                      in check (headU srt) (tailU srt)
 where
 check e arr | nullU arr = property True
             | otherwise = f e <= f (headU arr) .&. check (headU arr) (tailU arr)
-}

longGen :: (Arbitrary e) => Int -> Gen (Vector e)
longGen k = liftM2 (\l r -> V.fromList (l ++ r)) (vectorOf k arbitrary) arbitrary

sanity :: Int
sanity = 100

prop_partialsort :: (Ord e, Arbitrary e, Show e)
                 => (forall s mv. G.MVector mv e => mv s e -> Int -> ST s ())
                 -> Positive Int -> Property
prop_partialsort = prop_sized $ \algo k ->
  prop_sorted . V.take k . modify algo

prop_sized_empty :: (Ord e) => (forall s. MV.MVector s e -> Int -> ST s ()) -> Property
prop_sized_empty algo = prop_empty (flip algo 0) .&&. prop_empty (flip algo 10)

prop_select :: (Ord e, Arbitrary e, Show e)
            => (forall s mv. G.MVector mv e => mv s e -> Int -> ST s ())
            -> Positive Int -> Property
prop_select = prop_sized $ \algo k arr ->
  let vec' = modify algo arr
      l    = V.slice 0 k vec'
      r    = V.slice k (V.length vec' - k) vec'
  in V.all (\e -> V.all (e <=) r) l

prop_sized :: (Arbitrary e, Show e, Testable prop)
           => ((forall s mv. G.MVector mv e => mv s e -> ST s ())
                 -> Int -> Vector e -> prop)
           -> (forall s mv. G.MVector mv e => mv s e -> Int -> ST s ())
           -> Positive Int -> Property
prop_sized prop algo (Positive k) =
  let k' = k `mod` sanity
  in forAll (longGen k') $ prop (\marr -> algo marr k') k'

prop_stable :: (forall e s mv. G.MVector mv e => Comparison e -> mv s e -> ST s ())
            -> Vector Int -> Property
-- prop_stable algo arr = property $ modify algo arr == arr
prop_stable algo arr = stable $ modify (algo (comparing fst)) $ V.zip arr ix
 where
 ix = V.fromList [1 .. V.length arr]

stable arr | V.null arr = property True
           | otherwise  = let (e, i) = V.head arr
                          in V.all (\(e', i') -> e < e' || i < i') (V.tail arr)
                            .&. stable (V.tail arr)

prop_stable_radix :: (forall e s mv. G.MVector mv e => Int -> Int -> (Int -> e -> Int) 
                        -> mv s e -> ST s ())
                  -> Vector Int -> Property
prop_stable_radix algo arr =
  stable . modify (algo (passes e) (size e) (\k (e, _) -> radix k e))
         $ V.zip arr ix
 where
 ix = V.fromList [1 .. V.length arr]
 e = V.head arr
 
prop_optimal :: Int
             -> (forall e s mv. G.MVector mv e => Comparison e -> mv s e -> Int -> ST s ())
             -> Property
prop_optimal n algo = label "sorting" sortn .&. label "stability" stabn
 where
 arrn  = V.fromList [0..n-1]
 sortn = all ( (== arrn)
             . modify (\a -> algo compare a 0)
             . V.fromList)
         $ permutations [0..n-1]
 stabn = all ( (== arrn)
             . snd
             . V.unzip
             . modify (\a -> algo (comparing fst) a 0))
         $ stability n

type Bag e = M.Map e Int

toBag :: (Ord e) => Vector e -> Bag e
toBag = M.fromListWith (+) . flip zip (repeat 1) . V.toList

prop_permutation :: (Ord e) => (forall s mv. G.MVector mv e => mv s e -> ST s ())
                 -> Vector e -> Property
prop_permutation algo arr = property $ 
                            toBag arr == toBag (modify algo arr)

newtype SortedVec e = Sorted (Vector e)

instance (Show e) => Show (SortedVec e) where
  show (Sorted a) = show a

instance (Arbitrary e, Ord e) => Arbitrary (SortedVec e) where
  arbitrary = fmap (Sorted . V.fromList . sort)
                $ liftM2 (++) (vectorOf 20 arbitrary) arbitrary

ixRanges :: Vector e -> Gen (Int, Int)
ixRanges vec = do i <- fmap (`mod` len) arbitrary
                  j <- fmap (`mod` len) arbitrary
                  return $ if i < j then (i, j) else (j, i)
 where len = V.length vec

prop_search_inrange :: (Ord e)
                    => (forall s. MVector s e -> e -> Int -> Int -> ST s Int)
                    -> SortedVec e -> e -> Property
prop_search_inrange algo (Sorted arr) e = forAll (ixRanges arr) $ \(i, j) ->
  let k = runST (mfromList (V.toList arr) >>= \marr -> algo marr e i j)
  in property $ i <= k && k <= j
 where
 len = V.length arr

prop_search_insert :: (e -> e -> Bool) -> (e -> e -> Bool)
                   -> (forall s. MVector s e -> e -> ST s Int)
                   -> SortedVec e -> e -> Property
prop_search_insert lo hi algo (Sorted arr) e =
  property $ (k == 0   || (arr V.! (k-1)) `lo` e)
          && (k == len || (arr V.! k) `hi` e)
 where
 len = V.length arr
 k = runST (mfromList (V.toList arr) >>= \marr -> algo marr e)

prop_search_lowbound :: (Ord e)
                     => (forall s. MVector s e -> e -> ST s Int)
                     -> SortedVec e -> e -> Property
prop_search_lowbound = prop_search_insert (<) (>=)

prop_search_upbound :: (Ord e)
                    => (forall s. MVector s e -> e -> ST s Int)
                    -> SortedVec e -> e -> Property
prop_search_upbound = prop_search_insert (<=) (>)
