module GhcSort where

import Language.Haskell.Liquid.Prelude

{-@ type OList a =  [a]<{\fld v -> (v >= fld)}>  @-}


{-@ assert sort2 :: (Ord a) => [a] -> OList a  @-}
sort2 :: (Ord a) => [a] -> [a]
sort2 = mergesort

mergesort :: (Ord a) => [a] -> [a]
mergesort = mergesort' . map wrap

mergesort' :: (Ord a) => [[a]] -> [a]
mergesort' [] = []
mergesort' [xs] = xs
mergesort' xss = mergesort' (merge_pairs xss)

{-@ predicate DLen X Y = 
    (if ((len X) > 1) 
     then ((len Y) < (len X)) 
     else ((len X) = (len Y))) 
  @-}

{-@ merge_pairs :: (Ord a) => xs:[OList a] -> {v:[OList a] | (DLen xs v)} @-}
merge_pairs :: (Ord a) => [[a]] -> [[a]]
merge_pairs [] = []
merge_pairs [xs] = [xs]
merge_pairs (xs:ys:xss) = merge xs ys d : merge_pairs xss
  where d = length xs + length ys


{-@ Decrease merge 4 @-}
{-@ merge :: (Ord a) => xs:OList a -> ys:OList a -> {n:Nat|n = (len xs) + (len ys)} -> OList a  @-}
merge :: (Ord a) => [a] -> [a] -> Int -> [a]
merge [] ys _ = ys
merge xs [] _ = xs
merge (x:xs) (y:ys) d
 = case x `compare` y of
        GT -> y : merge (x:xs)   ys (d-1)
        _  -> x : merge xs   (y:ys) (d-1)

wrap :: a -> [a]
wrap x = [x]


