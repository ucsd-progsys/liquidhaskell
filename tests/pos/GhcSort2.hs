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

merge_pairs :: (Ord a) => [[a]] -> [[a]]
merge_pairs [] = []
merge_pairs [xs] = [xs]
merge_pairs (xs:ys:xss) = merge xs ys : merge_pairs xss

merge :: (Ord a) => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys)
 = case x `compare` y of
        GT -> y : merge (x:xs)   ys
        _  -> x : merge    xs (y:ys)

wrap :: a -> [a]
wrap x = [x]


