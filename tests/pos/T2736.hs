-- The autosize measure reaches the solver under the name it is declared with in
-- GHC.Base_LHAssumptions. The signature below keeps a constraint that mentions
-- it; with an unqualified name that constraint is rejected as having a free
-- variable.
module T2736 where

data List a = N | Cons a (List a)

{-@ autosize List @-}

{-@ sizeList :: List a -> Nat @-}
sizeList :: List a -> Int
sizeList N           = 0
sizeList (Cons _ xs) = 1 + sizeList xs
