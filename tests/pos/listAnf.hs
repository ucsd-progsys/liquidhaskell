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

{-@ invariant {v: List a | (llen v) >= 0}@-}

data List a 
   = Nil 
   | Cons a (List a)

checkSort Nil                        = True
checkSort (_ `Cons` Nil)             = True
checkSort (x1 `Cons` (x2 `Cons` xs)) = liquidAssertB (x1 <= x2) && checkSort (x2 `Cons` xs)

z3 :: List Integer 
z3    = 3 `Cons` (6 `Cons` Nil)
prop3 = checkSort z3

-- The below works because it is properly ANF-ed
-- The above fails because the "3" is not hoisted out into its own binding.

--three :: Integer
--three = 3
--
--six :: Integer
--six = 6
--
--z2 :: List Integer 
--z2    = three `Cons` (six `Cons` Nil) 
--prop2 = checkSort z2


















































