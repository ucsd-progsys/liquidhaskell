------------------------------------------------------------------------------
-- | An implementation of Merge Sort, where LH verifies
--   * termination, and that
--   * the output is an ordered permutation of the input.
------------------------------------------------------------------------------

module MergeSort (bag, sort) where

import qualified Language.Haskell.Liquid.Bag as B

{-@ measure bag @-}
bag :: (Ord a) => [a] -> B.Bag a
bag []     = B.empty
bag (x:xs) = B.put x (bag xs)

{-@ type OList a    = [a]<{\fld v -> (v >= fld)}>       @-}
{-@ type OListN a N = {v:OList a | len v == N}          @-}
{-@ type OListBag a B = {v:OList a | bag v == B} @-}

--------------------------------------------------------------------------------
-- | The top level `sort` function. Proved:
--    *  ordered, and
--    *  same multi-set as the input.
--------------------------------------------------------------------------------
{-@ sort :: (Ord a) => xs:[a] -> OListBag a (bag xs) @-}
sort :: Ord a => [a] -> [a]
sort []   = []
sort [x]  = [x]
sort xs   = merge (sort xs1) (sort xs2)
  where
    (xs1, xs2) = split xs

--------------------------------------------------------------------------------
-- | The `split` function breaks its list into two `Halves`:
--------------------------------------------------------------------------------
{-@ split :: xs:[a] -> Halves a xs @-}
split :: [a] -> ([a], [a])
split (x:(y:zs)) = (x:xs, y:ys) where (xs, ys) = split zs
split xs         = (xs, [])


-- | A type describing two `Halves` of a list `Xs`
{-@ type Halves a Xs = {v: (Half a Xs, Half a Xs) | len (fst v) + len (snd v) = len Xs && B.union (bag (fst v)) (bag (snd v)) == bag Xs}
  @-}

-- | Each `Half` is empty or smaller than the input:
{-@ type Half a Xs  = {v:[a] | (len v > 1) => (len v < len Xs)} @-}

--------------------------------------------------------------------------------
-- | Finally, the `merge` function combines two ordered lists.
--------------------------------------------------------------------------------
{-@ merge :: Ord a => xs:OList a -> ys:OList a -> OListBag a (B.union (bag xs) (bag ys)) / [(len xs + len ys)] @-}
merge :: Ord a => [a] -> [a] ->  [a]
merge xs []         = xs
merge [] ys         = ys
merge (x:xs) (y:ys)
  | x <= y          = x : merge xs (y:ys)
  | otherwise       = y : merge (x:xs) ys
