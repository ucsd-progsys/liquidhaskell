module ListRange where

import Language.Haskell.Liquid.Prelude



chk y = 
  case y of 
   Nil -> True
   Cons x1 xs -> case xs of 
                 Nil -> True
                 Cons x2 xs2 -> assert (x1 <= x2) && chk xs
																	
bar1 = insert 2 (insert 4 Nil)
bar2 = mkList [1 .. 10]

mkList :: Ord a => [a] -> List a
mkList = foldr insert Nil

prop1 = chk bar1
prop2 = chk bar2
