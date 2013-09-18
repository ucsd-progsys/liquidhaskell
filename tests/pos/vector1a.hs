module Vec1 where

import Language.Haskell.Liquid.Prelude
import Data.Vector hiding (map, concat, zipWith, filter, foldr, foldl, (++))


{-@ invariant {v:Int | v >= 0} @-}
for :: Int -> Int -> a -> (Int -> a -> a) -> a
for lo hi  = for' (hi-lo) lo hi

for' :: Int -> Int -> Int -> a -> (Int -> a -> a) -> a
for' d lo hi acc f 
  | lo < hi   = for' (d-1) (lo + 1) hi (f lo acc) f
  | otherwise = acc 

dotProd       :: Vector Int -> Vector Int -> Int
dotProd v1 v2 = for 0 n 0 $ \i -> (((v1!i) * (v2!i)) +)
  where n = Data.Vector.length v1

sumSquare   :: Vector Int -> Int
sumSquare v = dotProd v v

total = sumSquare $ Data.Vector.fromList [0..100]
