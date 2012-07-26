module ListSort where

import Language.Haskell.Liquid.Prelude -- (liquidAssertB, choose)

-- insertSort :: (Ord a) => [a] -> [a]
insertSort                    = foldr insert []

insert y []                   = [y]
insert y (x : xs) | y <= x    = y : x : xs 
                  | otherwise = x : insert y xs

-- checkSort ::  (Ord a) => [a] -> Bool
checkSort []                  = liquidAssertB True
checkSort [_]                 = liquidAssertB True
checkSort (x1:x2:xs)          = liquidAssertB (x1 <= x2) && checkSort (x2:xs)

-----------------------------------------------------------------------

bar   = insertSort rlist
rlist = map choose [1 .. 10]

bar1  :: [Int]
bar1  = [1, 2, 4, 5]

prop0 = checkSort bar
prop1 = checkSort bar1
-- prop2 = checkSort [3, 1, 2] 
