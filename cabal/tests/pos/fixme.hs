module ListRange where

import Language.Haskell.Liquid.Prelude

{-@  
data List a <p :: a -> a -> Bool>  
  = Nil 
  | Cons (h :: a) (t :: List <p> (a <p h>))
@-}

data List a 
   = Nil 
   | Cons a (List a)

checkSort Nil                        = True
checkSort (_ `Cons` Nil)             = True
checkSort (x1 `Cons` (x2 `Cons` xs)) = assert (x1 <= x2) && checkSort (x2 `Cons` xs)

xs1   = 3 `Cons` (6 `Cons` Nil) 
prop1 = checkSort xs1 

-- ADD THIS AND ITS SAT! WTF!
-- Because the ANF puts temp-names for 3 and 6 in scope making the above
-- sorted (pure accident).

xs2   = 3 `Cons` (6 `Cons` Nil) 



















































