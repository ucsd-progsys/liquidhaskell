module ListRange () where
{-@ LIQUID "--no-termination" @-}

import Language.Haskell.Liquid.Prelude

{-@  
data List a <p :: x0:a -> x1:a -> Prop>  
  = Nil 
  | Cons (h :: a) (t :: List <p> (a <p h>))
@-}
data List a = Nil | Cons a (List a)


-- This is needed to conclude that 
-- xs = Nil /\ xs = Cons _ _ <=> false

{-@ measure llen :: (List a) -> Int
    llen(Nil)       = 0
    llen(Cons x xs) = 1 + (llen xs)
  @-}

{-@ invariant {v:List a | (llen v) >= 0} @-}

split :: List a -> (List a, List a)
split (Cons x (Cons y zs)) = (Cons x xs, Cons y ys) where (xs, ys) = split zs
split xs                   = (xs, Nil)


{-@ Lazy merge @-}
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
                  Cons x2 xs2 -> liquidAssertB (x1 <= x2) && chk xs2
																	
bar = mergesort $ mkList [1 .. 100]

barI :: List Int
barI = Cons 1 $ Cons 2 $ Cons 3 Nil

mkList :: Ord a => [a] -> List a
mkList = foldr Cons Nil

prop0 = chk bar
prop1 = chk barI
