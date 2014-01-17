module ListClone () where

import Language.Haskell.Liquid.Prelude

make2d :: a -> Int -> Int -> [[a]]
make2d x n m = clone (clone x n) m

clone :: a -> Int -> [a]
clone x n
  | n == 0
  = []
  | otherwise 
  = x : (clone x (n-1))



-- check [] = [liquidAssertB True]
-- check (xs:xss) = let n = length xs in map (\xs' -> liquidAssertB (length xs' == n)) xss

chk [] = liquidAssertB True
chk (xs:xss) =
  case xss of 
   (xs1:xss1) -> let n = length xs in liquidAssertB (length xs1 == n) && chk xss
   []         -> liquidAssertB True

fooL  = [[1, 1, 3], [2, 2, 5]]
fooL1 = let f = make2d n0 n1 n2 in f
    where n0 = 0
          n1 = 2
          n2 = 3
propL = chk fooL1
prop  = chk fooL






































