module ListISort_LType (llen) where

import Language.Haskell.Liquid.Prelude

--------------------------------------------------------------------
-------------- Defining A List Type --------------------------------
--------------------------------------------------------------------

{-@ data List [llen] a <p :: x0:a -> x1:a -> Bool>  
      = Nil 
      | Cons { lHd :: a, lTl :: List <p> (a <p lHd>) }
  @-}

{-@ measure llen @-}
llen :: (List a) -> Int
{-@ llen :: List a -> Nat @-}
llen Nil         = 0
llen (Cons x xs) = 1 + (llen xs)

data List a 
  = Nil 
  | Cons a (List a)

checkSort Nil                        
  = True
checkSort (_ `Cons` Nil)             
  = True
checkSort (x1 `Cons` (x2 `Cons` xs)) 
  = liquidAssertB (x1 <= x2) && checkSort (x2 `Cons` xs)

xs0 :: List Int
xs0   = Nil
prop0 = checkSort xs0

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

insertSort = foldr insert Nil

bar3 = insertSort $ map choose [1 .. 10]
prop3 = checkSort bar3
