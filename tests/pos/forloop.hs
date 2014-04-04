module Vec1 () where

{-@ LIQUID "--no-termination" @-}
import Language.Haskell.Liquid.Prelude

mmax x y 
  | x < y     = y
  | otherwise = x

for lo hi acc f 
  | lo < hi   = for (lo + 1) hi (f lo acc) f
  | otherwise = acc 

sumRange i j = for i j 0 (+)

prop = liquidAssertB (m >= 0)
  where m = sumRange 0 k
        k = choose 0

prop2 = liquidAssertB (z >= x && z >= y)
  where x = choose 0
        y = choose 1
        z = mmax x y
