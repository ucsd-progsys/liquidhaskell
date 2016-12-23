module CoreToLog where

import Data.Set

-- ISSUE: can we please allow things like `empty` to also
-- appear in type and alias specifications, not just in
-- measures as in `goo` below?

{- type IsEmp a = {v:[a] | Data.Set.elems v = Data.Set.empty } @-}
{-@ type IsEmp a = {v:[a] | Data.Set.elems v = Data.Set.empty 10 } @-}

{-@ foo :: IsEmp Int @-}
foo :: [Int]
foo = []

{-@ predicate Data.Set.elems Xs = listElts Xs @-}
{-@ predicate Data.Set.empty X  = Set_empty 0 @-}

{-@ measure goo @-}
goo        :: (Ord a) => [a] -> Set a
goo []     = empty
goo (x:xs) = (singleton x) `union` (goo xs)
