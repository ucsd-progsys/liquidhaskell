module ListSort () where

import Language.Haskell.Liquid.Prelude

app k []     ys = k:ys
app k (x:xs) ys = x:(app k xs ys) 

takeL x []     = []
takeL x (y:ys) = if (y<x) then y:(takeL x ys) else takeL x ys

takeGE x []     = []
takeGE x (y:ys) = if (y>=x) then y:(takeGE x ys) else takeGE x ys


{-@ quicksort :: (Ord a) => xs:[a] -> [a]<{\fld v -> (v >= fld)}>  @-}
quicksort []     = []
quicksort (x:xs) = app x xsle xsge
  where xsle = quicksort (takeL x xs)
        xsge = quicksort (takeGE x xs)

{-@ qsort :: (Ord a) => xs:[a] -> [a]<{\fld v -> (v >= fld)}>  @-}
qsort []     = []
qsort (x:xs) = app x (qsort [y | y <- xs, y < x]) (qsort [z | z <- xs, z >= x]) 

-------------------------------------------------------------------------------

chk [] = liquidAssertB True
chk (x1:xs) = case xs of 
               []     -> liquidAssertB True
               x2:xs2 -> liquidAssertB (x1 <= x2) && chk xs
																	
prop0 = chk bar
  where 
    rlist = map choose [1 .. 10]
    bar = quicksort rlist




