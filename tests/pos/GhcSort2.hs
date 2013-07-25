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
merge_pairs (xs:ys:xss) = merge d xs ys : merge_pairs xss
  where d = length xs + length ys

merge :: (Ord a) => Int -> [a] -> [a] -> [a]
merge _ [] ys = ys
merge _ xs [] = xs
merge d (x:xs) (y:ys)
 = case x `compare` y of
        GT -> y : merge (d-1) (x:xs)   ys
        _  -> x : merge (d-1) xs   (y:ys)

wrap :: a -> [a]
wrap x = [x]


