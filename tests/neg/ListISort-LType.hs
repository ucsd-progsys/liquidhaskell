module ListRange () where

import Language.Haskell.Liquid.Prelude


data List a = Nil | Cons a (List a)

-- isOdd x = not (isEven x)
-- isEven x = not (isOdd x)

-- foo x = x+1

insert y Nil         
  = Cons y Nil
insert y (Cons x xs) | (y <= x) 
  = let ys1 = Cons x xs in
    let ys2 = Cons y ys1 in ys2
insert y (Cons x xs) | (x <  y)
  = let xs1 = insert y xs in
    let xs2 = Cons x xs1 in xs2

chk2 y = 
  case y of 
   Nil -> True
   Cons x1 xs -> case xs of 
                 Nil -> True
                 Cons x2 xs2 -> liquidAssertB (x1 == x2) && chk2 xs2
																	
n, m :: Int
n = choose 0
m = choose 0

-- bar = insert n (range 2 8)
bar = insert n (insert m Nil)

range l h = if l <=h then Cons l (range (l+1) h) else Nil


mkList :: [a] -> List a																	
mkList = foldr Cons Nil

prop0 = chk2 bar










