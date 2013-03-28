module ListSort where

import Language.Haskell.Liquid.Prelude -- (liquidAssertB, choose)

{-@ type OList a = [a]<{\fld v -> (v >= fld)}> @-}
{-@ assert sort1 :: (Ord a) => [a] -> OList a  @-}
sort1 :: (Ord a) => [a] -> [a]
sort1 = mergeAll . sequences
  where
    sequences (a:b:xs)
      | a `compare` b == GT = descending b [a]  xs
      | otherwise           = ascending  b (a:) xs
    sequences [x] = [[x]]
    sequences []  = [[]]

    descending a as (b:bs)
      | a `compare` b == GT = descending b (a:as) bs
    descending a as bs      = (a:as): sequences bs

    ascending a as (b:bs)
      | a `compare` b /= GT = ascending b (\ys -> as (a:ys)) bs
    ascending a as bs       = as [a]: sequences bs

    mergeAll [x] = x
    mergeAll xs  = mergeAll (mergePairs xs)

    mergePairs (a:b:xs) = merge1 a b: mergePairs xs
    mergePairs [x]      = [x]
    mergePairs []       = []

-- merge1 needs to be toplevel,
-- to get applied transformRec tx
merge1 (a:as') (b:bs')
  | a `compare` b == GT = b:merge1 (a:as')  bs'
  | otherwise           = a:merge1 as' (b:bs')
merge1 [] bs            = bs
merge1 as []            = as


