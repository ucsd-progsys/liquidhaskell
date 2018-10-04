-- TODO-REBARE: get this to work with "--structural" to check termination of the gnarly mutually-rec stuff; 
-- and plain metrics to do "merge1"

{-@ LIQUID "--structural" @-}

{-# Language ScopedTypeVariables   #-}
{-# Language PartialTypeSignatures #-}

module ListSort () where

import Language.Haskell.Liquid.Prelude 

{-@ type OList a = [a]<{\fld v -> (v >= fld)}> @-}
{-@ assert sort1 :: (Ord a) => [a] -> OList a  @-}
sort1 :: (Ord a) => [a] -> [a]
sort1 xs = mergeAll  (sequences xs 0)
  where
    {- decrease sequences  2 3 @-}
    {- decrease descending 4 5 @-}
    {- decrease ascending  4 5 @-}

    {- sequences :: _ -> as:[_] -> n:Nat -> [[_]] / [len as, n] @-}
    sequences :: [_] -> Int -> [[_]]
    sequences (a:b:xs) (_::Int)
      | a `compare` b == GT = descending b [a]  xs 1
      | otherwise           = ascending  b (a:) xs 1
    sequences [x] _ = [[x]]
    sequences []  _ = [[]]

    {- descending :: _ -> _ -> _ -> bs:[_] -> m:Nat -> [[_]] / [len bs, m] @-}
    descending :: _ -> _ -> [_] -> Int -> [[_]]
    descending a as (b:bs) (_::Int)
      | a `compare` b == GT = descending b (a:as) bs 1
    descending a as bs _    = (a:as): sequences bs 0

    {- ascending :: _ -> _ -> _ -> bs:[_] -> m:Nat -> [[_]] / [len bs, m] @-}
    ascending :: _ -> _ -> [_] -> Int -> [[_]]
    ascending a as (b:bs) (_ :: Int)
      | a `compare` b /= GT = ascending b (\ys -> as (a:ys)) bs 1
    ascending a as bs _     = as [a]: sequences bs 0

    mergeAll []  = [] --this case cannot occur, though
    mergeAll [x] = x
    mergeAll xs  = mergeAll (mergePairs xs)

{-@ mergePairs :: Ord a
               => xss:[(OList a)]
               -> {v:[(OList a)] | (if ((len xss) > 1) then ((len v) < (len xss)) else ((len v) = (len xss) ))}
  @-}
mergePairs :: Ord a => [[a]] -> [[a]]
mergePairs (a:b:xs) = merge1 a b: mergePairs xs
mergePairs [x]      = [x]
mergePairs []       = []

-- merge1 needs to be toplevel,
-- to get applied transformRec tx


{-@ lazy merge1 @-}  -- TODO-REBARE: this is a hack; we should use plain metrics for when STRUCTURAL can't deal with it. 

{-@ merge1 :: Ord a
           => xs:OList a
           -> ys:OList a
           -> {v:OList a | len v == len xs + len ys}
           / [len xs + len ys]
  @-}
merge1 :: Ord a => [a] -> [a] -> [a]
merge1 (a:as') (b:bs')
  | a `compare` b == GT = b:merge1 (a:as')  bs'
  | otherwise           = a:merge1 as' (b:bs')
merge1 [] bs            = bs
merge1 as []            = as
