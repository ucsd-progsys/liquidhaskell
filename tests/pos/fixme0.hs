module ListSort  where

{-@ type COList a = [a]<\fld -> {v:a | v >= fld}>  @-}
{-@ type OList a = [a]<{\fld v -> (v >= fld)}>  @-}

{-@ mergesort :: COList a -> OList a @-}
mergesort :: [a] -> [a]
mergesort []  = []

