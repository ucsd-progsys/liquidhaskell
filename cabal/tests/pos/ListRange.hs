module ListRange where

import Language.Haskell.Liquid.Prelude


data List a = Nil | Cons a (List a)

low, high :: Int
low  = 0
high = 10

lst = range low high	

range l h = 
  if l <= h then Cons l (range (l+1) h) else Nil

chk Nil                    = assert True
chk (Cons x Nil)           = assert True
chk (Cons x1 (Cons x2 xs)) = assert (x1 <= x2) && chk (Cons x2 xs)


prop3 = chk           lst
