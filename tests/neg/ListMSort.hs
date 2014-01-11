module ListSort () where

import Language.Haskell.Liquid.Prelude


split :: [a] -> ([a], [a])
split (x:(y:zs)) = (x:xs, y:ys) where (xs, ys) = split zs
split xs                   = (xs, [])

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
  | x <= y
  = x:(merge xs (y:ys))
  | otherwise 
  = y:(merge (x:xs) ys)

{-@ mergesort :: (Ord a) => xs:[a] -> [a]<{\fld v -> (v < fld)}>  @-}
mergesort :: Ord a => [a] -> [a]
mergesort [] = []
mergesort [x] = [x]
mergesort xs = merge (mergesort xs1) (mergesort xs2) where (xs1, xs2) = split xs

chk [] = liquidAssertB True
chk (x1:xs) = case xs of 
               []     -> liquidAssertB True
               x2:xs2 -> liquidAssertB (x1 <= x2) && chk xs
																	
rlist = map choose [1 .. 10]

bar = mergesort rlist

prop0 = chk bar
