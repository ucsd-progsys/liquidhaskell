{-@ LIQUID "--no-termination" @-}

module GhcSort () where

import Language.Haskell.Liquid.Prelude

{-@ type OList a =  [a]<{\fld v -> (v >= fld)}>  @-}
{-@ type DList a =  [a]<{\fld v -> (fld >= v)}>  @-}

---------------------------------------------------------------------------
---------------------------  Official GHC Sort ----------------------------
---------------------------------------------------------------------------

{-@ sort1 :: (Ord a) => [a] -> OList a  @-}
sort1 :: (Ord a) => [a] -> [a]
sort1 = mergeAll . sequences
  where
    sequences (a:b:xs)
      | a `compare` b == GT = descending b [a]  xs
      | otherwise           = ascending  b (a:) xs -- a >= b => (a:) ->   
    sequences [x] = [[x]]
    sequences []  = [[]]
    {- descending :: x:a -> OList {v:a | x < v} -> [a] -> [OList a] @-}
    descending a as (b:bs)
      | a `compare` b == GT = descending b (a:as) bs
    descending a as bs      = (a:as): sequences bs

    {- ascending :: x:a -> (OList {v:a|v>=x} -> OList a) -> [a] -> [OList a] @-}
    ascending a as (b:bs)
      | a `compare` b /= GT = ascending b (\ys -> as (a:ys)) bs -- a <= b
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

---------------------------------------------------------------------------
------------------- Mergesort ---------------------------------------------
---------------------------------------------------------------------------

{-@ sort2 :: (Ord a) => [a] -> OList a  @-}
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

----------------------------------------------------------------------
-------------------- QuickSort ---------------------------------------
----------------------------------------------------------------------

{-@ sort3 :: (Ord a) => w:a -> [{v:a|v<=w}] -> OList a @-}
sort3 :: (Ord a) => a -> [a] -> [a]
sort3 w ls = qsort w ls []

-- qsort is stable and does not concatenate.
qsort :: (Ord a) =>  a -> [a] -> [a] -> [a]
qsort _ []     r = r
qsort _ [x]    r = x:r
qsort w (x:xs) r = qpart w x xs [] [] r

-- qpart partitions and sorts the sublists
qpart :: (Ord a) => a -> a -> [a] -> [a] -> [a] -> [a] -> [a]
qpart w x [] rlt rge r =
    -- rlt and rge are in reverse order and must be sorted with an
    -- anti-stable sorting
    rqsort x rlt (x:rqsort w rge r)
qpart w x (y:ys) rlt rge r =
    case compare x y of
        GT -> qpart w x ys (y:rlt) rge r
        _  -> qpart w x ys rlt (y:rge) r

-- rqsort is as qsort but anti-stable, i.e. reverses equal elements
rqsort :: (Ord a) => a -> [a] -> [a] -> [a]
rqsort _ []     r = r
rqsort _ [x]    r = x:r
rqsort w (x:xs) r = rqpart w x xs [] [] r

rqpart :: (Ord a) => a -> a -> [a] -> [a] -> [a] -> [a] -> [a]
rqpart w x [] rle rgt r =
    qsort x rle (x:qsort w rgt r)
rqpart w x (y:ys) rle rgt r =
    case compare y x of
        GT -> rqpart w x ys rle (y:rgt) r
        _  -> rqpart w x ys (y:rle) rgt r













