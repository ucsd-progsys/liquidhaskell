module ListSort () where

import Language.Haskell.Liquid.Prelude

{-@ type OList a = [a]<{\fld v -> (v >= fld)}>  @-}

{-@ predicate Pr X Y = (((len Y) > 1) => ((len Y) < (len X))) @-}

{-@ split :: xs:[a] 
          -> ({v:[a] | (Pr xs v)}, {v:[a]|(Pr xs v)})
                 <{\x y -> ((len x) + (len y) = (len xs))}> 
  @-}

split :: [a] -> ([a], [a])
split (x:(y:zs)) = (x:xs, y:ys) where (xs, ys) = split zs
split xs                   = (xs, [])


{-@ Decrease merge 4 @-}
{-@ merge :: Ord a => xs:(OList a) -> ys:(OList a) -> d:{v:Int| v = (len xs) + (len ys)} -> {v:(OList a) | (len v) = d} @-}
merge :: Ord a => [a] -> [a] -> Int -> [a]
merge xs [] _ = xs
merge [] ys _ = ys
merge (x:xs) (y:ys) d
  | x <= y
  = x:(merge xs (y:ys) (d-1))
  | otherwise 
  = y:(merge (x:xs) ys (d-1))

{-@ mergesort :: (Ord a) => xs:[a] -> {v:(OList a) | (len v) = (len xs)}  @-}
mergesort :: Ord a => [a] -> [a]
mergesort []  = []
mergesort [x] = [x]
mergesort xs  = merge (mergesort xs1) (mergesort xs2) d 
  where (xs1, xs2) = split xs
        d          = length xs

