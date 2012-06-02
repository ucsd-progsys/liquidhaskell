module ListSort where

import Language.Haskell.Liquid.Prelude -- (assert, choose)

insertSort = foldr insert []

insert y []       = [y]
insert y (x : xs) = if (y <= x) 
                      then (y : ( x : xs)) 
                      else (x : (insert y xs))


checkSort []      = assert True
checkSort (x1:xs) = case xs of 
                      []     -> assert True
                      x2:xs2 -> assert (x1 <= x2) && checkSort xs
																	

bar   = insertSort rlist
rlist = map choose [1 .. 10]

bar1  :: [Int]
bar1  = [1, 2, 4, 5]

prop0 = checkSort bar
prop1 = checkSort bar1
