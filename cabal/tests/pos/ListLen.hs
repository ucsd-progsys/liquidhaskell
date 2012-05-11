module ListClone where

import Language.Haskell.Liquid.Prelude

make2d :: a -> Int -> Int -> [[a]]
make2d x n m = clone (clone x n) m

clone :: a -> Int -> [a]
clone x n
  | n == 0
  = []
  | otherwise 
  = x : (clone x (n-1))

check [] = [assert True]
check (xs:xss) = let n = length xs in map (\xs' -> assert (length xs' == n)) xss

chk [] = assert True
chk (xs:xss) =
  case xss of 
   (xs1:xss1) -> let n = length xs in assert (length xs1 == n) && chk xss
   []         -> assert True

fooL  = [[1, 1, 3], [2, 2, 5]]
fooL1 = make2d 0 2 3

propL = chk fooL1
prop  = chk fooL
