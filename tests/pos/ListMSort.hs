module ListSort where

import Language.Haskell.Liquid.Prelude

{-@ predicate Pr X Y = (((len Y) > 1) => ((len Y) < (len X))) @-}

{-@ split :: xs:[a] 
          -> ({v:[a] | (Pr xs v)}, {v:[a]|(Pr xs v)})
                 <{\x y -> ((len x) + (len y) = (len xs))}> 
  @-}

split :: [a] -> ([a], [a])
split (x:(y:zs)) = (x:xs, y:ys) where (xs, ys) = split zs
split xs                   = (xs, [])

merge :: Ord a => Int -> [a] -> [a] -> [a]
merge _ xs [] = xs
merge _ [] ys = ys
merge d (x:xs) (y:ys)
  | x <= y
  = x:(merge (d-1) xs (y:ys))
  | otherwise 
  = y:(merge (d-1) (x:xs) ys)

{-@ mergesort :: (Ord a) => xs:[a] -> [a]<{\fld v -> (v >= fld)}>  @-}
mergesort :: Ord a => [a] -> [a]
mergesort []  = []
mergesort [x] = [x]
mergesort xs  = merge d (mergesort xs1) (mergesort xs2) 
  where (xs1, xs2) = split xs
        d          = length xs

