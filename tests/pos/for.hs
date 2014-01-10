module For (prop, prop2, even_, minifac) where

import Language.Haskell.Liquid.Prelude

even_ arg = if arg == 0 then True else odd_ (arg - 1)

odd_  arg = if arg == 0 then False else even_ (arg - 1)

mmax x y 
  | x < y     = y
  | otherwise = x

minifac foobar 
  | foobar > 1 =  minifac (foobar - 1)
  | otherwise  =  1

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
