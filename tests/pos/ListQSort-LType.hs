module ListRange () where

import Language.Haskell.Liquid.Prelude

{-@  
data List [llen] a <p :: x0:a -> x1:a -> Prop>  
  = Nil 
  | Cons (h :: a) (t :: List <p> (a <p h>))
@-}

{-@ measure llen :: (List a) -> Int
    llen(Nil)       = 0
    llen(Cons x xs) = 1 + (llen xs)
  @-}

{-@ invariant {v:List a | (llen v) >= 0} @-}

{-@ qualif ZLLen(v:List a) : (llen(v) >= 0)@-}
{-@ qualif CmpLLen(v:List a, A:List b) : ((llen v) <= (llen A))@-}

data List a = Nil | Cons a (List a)

append k Nil         ys = Cons k ys
append k (Cons x xs) ys = Cons x (append k xs ys) 

takeL x Nil         = Nil
takeL x (Cons y ys) = if (y<x) then Cons y (takeL x ys) else takeL x ys

{-@ takeGE :: Ord a 
           => x:a 
           -> xs:List a 
           -> {v: (List {v:a | v >= x}) | ((llen v) <= (llen xs))}  @-}
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
