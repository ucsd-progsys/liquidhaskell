module ListSort where

import Language.Haskell.Liquid.Prelude -- (liquidAssertB, choose)

{-@ type OList a = [a]<{v: a | (v >= fld)}> @-}

{-@ assert insertSort :: (Ord a) => xs:[a] -> {v: OList a | len(v) = len(xs)} @-}
insertSort        :: (Ord a) => [a] -> [a]
insertSort []     = []
insertSort (x:xs) = insert x (insertSort xs) 

{-@ assert insertSort' :: (Ord a) => xs:[a] -> OList a @-}
insertSort' xs                 = foldr insert [] xs

{-@ assert insert      :: (Ord a) => x:a -> xs: OList a -> {v: OList a | len(v) = (1 + len(xs)) } @-}
insert y []                   = [y]
insert y (x : xs) | y <= x    = y : x : xs 
                  | otherwise = x : insert y xs

-- checkSort ::  (Ord a) => [a] -> Bool
checkSort []                  = liquidAssertB True
checkSort [_]                 = liquidAssertB True
checkSort (x1:x2:xs)          = liquidAssertB (x1 <= x2) && checkSort (x2:xs)


-----------------------------------------------------------------------
--{- prop_sort1 :: (Ord a) => [a] -> Bool @-}
--prop_sort1 xs = checkSort (insertSort xs) 
--
--{- prop_sort2 :: (Ord a) => [a] -> Bool @-}
--prop_sort2 xs = checkSort (insertSort' xs) 



bar   = insertSort' rlist
rlist = map choose [1 .. 10]

bar1  :: [Int]
bar1  = [1, 2, 4, 5]

prop0 = checkSort bar
prop1 = checkSort bar1
-- prop2 = checkSort [3, 1, 2] 
