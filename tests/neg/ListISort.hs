module ListSort () where

import Language.Haskell.Liquid.Prelude

insert y []     = [y]
insert y (x:xs) = if (y<=x) then (y:(x:xs)) else (x:(insert y xs))

chk [] = liquidAssertB True
chk (x1:xs) = case xs of 
               []     -> liquidAssertB True
               x2:xs2 -> liquidAssertB (x1 <= x2) && chk xs
																	
sort = foldr insert []

rlist = map choose [1 .. 10]

bar = sort rlist

bar1 :: [Int]
bar1 = [1, 8, 2, 4, 5]

prop0 = chk rlist
prop1 = chk bar1
