module ListSort where

import Language.Haskell.Liquid.Prelude

append k []     ys = k:ys
append k (x:xs) ys = x:(append k xs ys) 

takeL x []     = []
takeL x (y:ys) = if (y<x) then y:(takeL x ys) else takeL x ys

takeGE x []     = []
takeGE x (y:ys) = if (y>=x) then y:(takeGE x ys) else takeGE x ys

quicksort []     = []
quicksort (x:xs) = append x xsle xsge
  where xsle = quicksort (takeL x xs)
        xsge = quicksort (takeGE x xs)

chk [] = liquidAssert True
chk (x1:xs) = case xs of 
               []     -> liquidAssert True
               x2:xs2 -> liquidAssert (x1 <= x2) && chk xs
																	
rlist = map choose [1 .. 10]

bar = quicksort rlist

prop0 = chk bar
