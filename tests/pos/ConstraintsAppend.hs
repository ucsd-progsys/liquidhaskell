module ConstraintsAppend () where

{-@ LIQUID "--no-termination" @-}

import Language.Haskell.Liquid.Prelude

{-@ type OList a = [a]<{\x v -> v >= x}> @-}


{-@ assume (++) :: forall <p :: a -> Bool, q :: a -> Bool, r :: a -> Bool>.
        {x::a<p> |- a<q> <: {v:a| x <= v}} 
        {a<p> <: a<r>} 
        {a<q> <: a<r>} 
        Ord a => OList (a<p>) -> OList (a<q>) -> OList a<r> @-}
{-@ app :: forall <p :: a -> Bool, q :: a -> Bool, r :: a -> Bool>.
        {x::a<p> |- a<q> <: {v:a| x <= v}} 
        {a<p> <: a<r>} 
        {a<q> <: a<r>} 
        Ord a => OList (a<p>) -> OList (a<q>) -> OList a<r> @-}
app :: Ord a => [a] -> [a] -> [a]
app []     ys = ys
app (x:xs) ys = x:(app xs ys) 

takeL :: Ord a => a -> [a] -> [a]
{-@ takeL :: Ord a => x:a -> [a] -> [{v:a|v<=x}] @-}
takeL x []     = []
takeL x (y:ys) = if (y<x) then y:(takeL x ys) else takeL x ys

takeGE :: Ord a => a -> [a] -> [a]
{-@ takeGE :: Ord a => x:a -> [a] -> [{v:a|v>=x}] @-}
takeGE x []     = []
takeGE x (y:ys) = if (y>=x) then y:(takeGE x ys) else takeGE x ys


{-@ quicksort :: (Ord a) => xs:[a] -> [a]<{\fld v -> (v >= fld)}>  @-}
quicksort []     = []
quicksort (x:xs) = xsle ++ (x:xsge)
  where xsle = quicksort (takeL x xs)
        xsge = quicksort (takeGE x xs)

{-@ qsort :: (Ord a) => xs:[a] -> [a]<{\fld v -> (v >= fld)}>  @-}
qsort []     = []
qsort (x:xs) = (qsort [y | y <- xs, y < x]) ++ (x:(qsort [z | z <- xs, z >= x])) 


