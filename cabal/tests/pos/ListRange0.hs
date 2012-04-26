module ListRange where

import Language.Haskell.Liquid.Prelude


data List a = Nil | Cons a (List a)

low, high :: Int
low  = 0
high = 10

lst = range low high	

range l h = 
  if l <= h then Cons l (range (l+1) h) else Nil

propRangeHead Nil = assert True
propRangeHead (Cons x xs) = assert ((x >= low) && (x <= high))

								
propRange Nil          
  = assert True
propRange (Cons x xs) 
  = assert ((x >= low) && (x <= high)) && (propRange xs)


prop1 = propRangeHead lst
prop2 = propRange     lst




{-
mymap f Nil         = Nil
mymap f (Cons x xs) = Cons (f x) (mymap f xs)

myfold f b Nil = error ""
myfold f b (Cons x Nil) = f x b
myfold f b (Cons x xs)   = f x (myfold f b xs)

chk Nil                    = assert True
chk (Cons x Nil)           = assert True
chk (Cons x1 (Cons x2 xs)) = assert (x1 <= x2) && chk (Cons x2 xs)


propS x (b, y) = (assert (x <=y), x)

propRange x = assert ((x >= low) && (x <= high))


prop2 = mymap propRange lst
-- prop3 = myfold propS (True, high) lst
prop3 = chk lst
-}


