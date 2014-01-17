module Vec1 () where

import Language.Haskell.Liquid.Prelude
import Data.Vector hiding (map, concat, zipWith, filter, foldr, foldl, (++))


-- HA this needs a non-TOP spec due to contravariance...
foo = (Data.Vector.!) 

for :: Int -> Int -> a -> (Int -> a -> a) -> a
for lo hi acc f 
  | lo < hi   = for (lo + 1) hi (f lo acc) f
  | otherwise = acc 

dotProd       :: Vector Int -> Vector Int -> Int
dotProd v1 v2 = for 0 n 0 $ \i -> (((v1!i) * (v2!i)) +)
  where n = Data.Vector.length v1

sumSquare   :: Vector Int -> Int
sumSquare v = dotProd v v

total = sumSquare $ Data.Vector.fromList [0..100]
