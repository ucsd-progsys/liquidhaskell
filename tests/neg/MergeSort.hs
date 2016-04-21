------------------------------------------------------------------------------
-- | An implementation of Merge Sort, where LH verifies:
--   1. Termination (Totality) 
--   2. The output is indeed in non-decreasing order 
------------------------------------------------------------------------------

module MergeSort (sort) where

{-@ type OList a    = [a]<{\fld v -> (v >= fld)}> @-}

{-@ type OListN a N = {v:OList a | len v == N} @-}

-- | The top level `sort` function. Proved:
--   (a) terminating, 
--   (b) ordered, and 
--   (c) of same size as input.

{-@ sort :: (Ord a) => xs:[a] -> OListN a {len xs} @-}
sort :: Ord a => [a] -> [a]
sort []   = []
sort [x]  = [x]
sort xs   = merge (sort xs1) (sort xs2) 
  where 
    (xs1, xs2) = split xs

-- Fun fact: if you delete the singleton case above,
-- the resulting function is, in fact, non-terminating!

-- | A type describing two `Halves` of a list `Xs` 

{-@ type Halves a Xs = {v: (Half a Xs, Half a Xs) | len (fst v) + len (snd v) == len Xs} @-}

-- | Each `Half` is empty or smaller than the input:

{-@ type Half a Xs  = {v:[a] | 2 * len v < 1 + len Xs} @-}

-- | The `split` function breaks its list into two `Halves`:

{-@ split :: xs:[a] -> Halves a xs @-}
split :: [a] -> ([a], [a])
split (x:(y:zs)) = (x:xs, y:ys) where (xs, ys) = split zs
split xs         = (xs, [])

-- | Finally, the `merge` function combines two ordered lists into a single ordered result.

{-@ merge :: Ord a => xs:OList a -> ys:OList a -> OListN a {len xs + len ys} / [(len xs + len ys)] @-}
merge :: Ord a => [a] -> [a] ->  [a]
merge xs []         = xs
merge [] ys         = ys
merge (x:xs) (y:ys)
  | x <= y          = x : merge xs (y:ys)
  | otherwise       = y : merge (x:xs) ys
