module Vec1 () where

{-@ LIQUID "--no-termination" @-}

import Language.Haskell.Liquid.Prelude
import Data.Vector hiding (map, concat, zipWith, filter, foldl, foldr, (++))

for lo hi acc f 
  | lo < hi   = for (lo + 1) hi (f lo acc) f
  | otherwise = acc 

dotProd v1 v2 = for 0 n 0 $ \i -> (((v1!i) * (v2!i)) +)
  where n = Data.Vector.length v1

sumSquare v = dotProd v v

total = sumSquare $ Data.Vector.fromList [0..100] -- nums
range i j = for i j [] (:)
nums  = range 0 100 -- [0..100]
