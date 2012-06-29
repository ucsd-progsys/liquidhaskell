module ListRange where

import Language.Haskell.Liquid.Prelude

--------------------------------------------------------------------
-------------- Defining A List Type --------------------------------
--------------------------------------------------------------------

{-@  
data List a <p :: a -> a -> Bool>  
  = Nil 
  | Cons (h :: a) (t :: List <p> (a <p h>))
@-}

data List a 
  = Nil 
  | Cons a (List a)


checkSort :: List Int -> Bool
checkSort Nil                        
  = True
checkSort (_ `Cons` Nil)             
  = True
checkSort (x1 `Cons` (x2 `Cons` xs)) 
  = assert (x1 <= x2) && checkSort (x2 `Cons` xs)

xs0 :: List Int
xs0   = Nil
prop0 = checkSort xs0

xs1 :: List Int 
xs1   = 4 `Cons` Nil
prop1 = checkSort xs1 

xs2 = 2 `Cons` (4 `Cons` Nil) 
prop2 = checkSort xs2 

----------------------------------------------------------------
----------------- Insertion Sort -------------------------------
----------------------------------------------------------------

insert y Nil                  
  = y `Cons` Nil 
insert y (Cons x xs) 
  | y <= x    = y `Cons` (x `Cons` xs) 
  | otherwise = x `Cons` (insert y xs)

mkList ::  Ord a => [a] -> List a
mkList = foldr insert Nil

bar3 = mkList $ map choose [1 .. 10]
prop3 = checkSort bar3


