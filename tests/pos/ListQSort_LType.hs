module ListQSort_LType (llen) where

import Language.Haskell.Liquid.Prelude

{-@
data List [llen] a <p :: x0:a -> x1:a -> Bool>
  = Nil
  | Cons { lHd :: a, lTl :: List <p> (a <p lHd>) }
@-}

{-@ measure llen @-}
llen :: (List a) -> Int
{-@ llen :: List a -> Nat @-}
llen Nil         = 0
llen (Cons x xs) = 1 + (llen xs)


{-@ qualif ZLLen(v:ListRange.List a) : (llen(v) >= 0)@-}

{-@ qualif CmpLLen(v:ListRange.List a, a:ListRange.List b) : (llen v <= llen a) @-}

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
