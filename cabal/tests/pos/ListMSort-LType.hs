module ListRange where

import Language.Haskell.Liquid.Prelude

{-@  
data List a <p :: a -> a -> Bool>  
  = Nil 
  | Cons (h :: a) (t :: List <p> (a <p h>))
@-}
data List a = Nil | Cons a (List a)

split :: List a -> (List a, List a)
split (Cons x (Cons y zs)) = (Cons x xs, Cons y ys) where (xs, ys) = split zs
split xs                   = (xs, Nil)

merge :: Ord a => List a -> List a -> List a
merge xs Nil = xs
merge Nil ys = ys
merge (Cons x xs) (Cons y ys)
  | x <= y
  = Cons x (merge xs (Cons y ys))
  | otherwise 
  = Cons y (merge (Cons x xs) ys)

mergesort :: Ord a => List a -> List a
mergesort Nil = Nil
mergesort (Cons x Nil) = Cons x Nil
mergesort xs = merge (mergesort xs1) (mergesort xs2) where (xs1, xs2) = split xs

chk y = 
  case y of 
   Nil -> True
   Cons x1 xs -> case xs of 
                  Nil -> True
                  Cons x2 xs2 -> liquidAssert (x1 <= x2) && chk xs2
																	
bar = mergesort $ mkList [1 .. 100]

barI :: List Int
barI = Cons 1 $ Cons 2 $ Cons 3 Nil

mkList :: Ord a => [a] -> List a
mkList = foldr Cons Nil

prop0 = chk bar
prop1 = chk barI
