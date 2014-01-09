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

{-@ invariant {v:(List a) | ((llen v) >= 0)} @-}

data List a = Nil | Cons a (List a)

{-
low, high :: Int
low  = 0
high = 10
-}

range l h = 
  if l <= h then Cons l (range (l+1) h) else Nil

chk y = 
  case y of 
   Nil -> True
   Cons x1 xs -> case xs of 
                 Nil -> True
                 Cons x2 xs2 -> liquidAssertB (x1 <= x2) && chk xs2

prop3 = chk $ range 1 100 
