module ListRange where

import Language.Haskell.Liquid.Prelude

{-@  
data List a <p :: x0:a -> x1:a -> Prop>  
  = Nil 
  | Cons (h :: a) (t :: List <p> (a <p h>))
@-}

data List a = Nil | Cons a (List a)

append k Nil         ys = Cons k ys
append k (Cons x xs) ys = Cons x (append k xs ys) 

takeL x Nil         = Nil
takeL x (Cons y ys) = if (y<x) then Cons y (takeL x ys) else takeL x ys

takeGE x Nil         = Nil
takeGE x (Cons y ys) = if (y>=x) then Cons y (takeGE x ys) else takeGE x ys

quicksort Nil = Nil
quicksort (Cons x xs) = append x xsle xsge
  where xsle = quicksort (takeL x xs)
        xsge = quicksort (takeGE x xs)

chk y = 
  case y of 
   Nil -> True
   Cons x1 xs -> case xs of 
                 Nil -> True
                 Cons x2 xs2 -> liquidAssertB (x1 <= x2) && chk xs
																	
bar = quicksort $ mkList [1 .. 100]

mkList :: Ord a => [a] -> List a
mkList = foldr Cons Nil

prop0 = chk bar
