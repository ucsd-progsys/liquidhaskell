module ListRange where

import Language.Haskell.Liquid.Prelude


data List a = Nil | Cons a (List a)

insert y Nil         = Cons y Nil
insert y (Cons x xs) = if (y < x) then (Cons y (Cons x xs)) else (Cons x (insert y xs))

chk2 y = 
  case y of 
   Nil -> True
   Cons x1 xs -> case xs of 
                 Nil -> True
                 Cons x2 xs2 -> assert (x1 <= x2) && chk2 xs2
																	
-- bar = insert 2 (insert 4 Nil)

bar = mkList [1 .. 10]

mkList :: Ord a => [a] -> List a
mkList = foldr insert Nil

prop0 = chk2 bar

