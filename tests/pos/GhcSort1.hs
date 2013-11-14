{-# Language ScopedTypeVariables #-}
module ListSort where

import Language.Haskell.Liquid.Prelude -- (liquidAssertB, choose)

{-@ type OList a = [a]<{\fld v -> (v >= fld)}> @-}
{-@ assert sort1 :: (Ord a) => [a] -> OList a  @-}
sort1 :: (Ord a) => [a] -> [a]
sort1 xs = mergeAll  (sequences xs 0)
  where
    {-@ Decrease sequences  1 2 @-}
    {-@ Decrease descending 3 4 @-}
    {-@ Decrease ascending  3 4 @-}
    sequences (a:b:xs) (_::Int)
      | a `compare` b == GT = descending b [a]  xs 1
      | otherwise           = ascending  b (a:) xs 1
    sequences [x] _ = [[x]]
    sequences []  _ = [[]]

    descending a as (b:bs) (_::Int)
      | a `compare` b == GT = descending b (a:as) bs 1
    descending a as bs _    = (a:as): sequences bs 0

    ascending a as (b:bs) (_ :: Int)
      | a `compare` b /= GT = ascending b (\ys -> as (a:ys)) bs 1
    ascending a as bs _     = as [a]: sequences bs 0

    mergeAll [x] = x
    mergeAll xs  = mergeAll (mergePairs xs)

    mergePairs (a:b:xs) = merge1 a b: mergePairs xs
    mergePairs [x]      = [x]
    mergePairs []       = []

-- merge1 needs to be toplevel,
-- to get applied transformRec tx

{-@ merge1 :: Ord a => xs:[a] -> ys:[a] -> [a] / [(len xs) + (len ys)] @-}
merge1 :: Ord a => [a] -> [a] -> [a]
merge1 (a:as') (b:bs')
  | a `compare` b == GT = b:merge1 (a:as')  bs'
  | otherwise           = a:merge1 as' (b:bs')
merge1 [] bs            = bs
merge1 as []            = as


