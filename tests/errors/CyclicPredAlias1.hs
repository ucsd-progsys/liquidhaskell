module Test1 () where

{-@ predicate CyclicB1 Q = CyclicB2 Q @-}
{-@ predicate CyclicB2 Q = CyclicB1 Q @-}

