module ListLen where

import Language.Haskell.Liquid.Prelude

{-@  
data List a <p :: x0:a -> x1:a -> Prop>  
  = Nil 
  | Cons (h :: a) (t :: List <p> (a <p h>))
@-}

data List a = Nil | Cons a (List a)

make2d :: a -> Int -> Int -> List ([a])
make2d x n m = cloneL (clone x n) m

clone :: a -> Int -> [a]
clone x n
  | n == 0
  = []
  | otherwise 
  = x : (clone x (n-1))

cloneL :: a -> Int -> List a
cloneL x n
  | n == 0
  = Nil
  | otherwise 
  = Cons x  (cloneL x (n-1))

check [] = [liquidAssertB True]
check (xs:xss) = let n = length xs in map (\xs' -> liquidAssertB (length xs' == n)) xss

chk Nil = liquidAssertB True
chk (Cons xs xss) =
  case xss of 
   (Cons xs1 xss1) -> let n = length xs in liquidAssertB (length xs1 == n) && chk xss
   Nil -> liquidAssertB True

fooL  = Cons [1, 1, 3] (Cons [2, 2, 5] Nil)
fooL1 = make2d 0 n m
  where n = choose 0
        m = choose 1

propL = chk fooL1
prop  = chk fooL
