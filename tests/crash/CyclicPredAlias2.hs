module Test2 () where

{-@ predicate CyclicC1 Q = CyclicC2 Q && CyclicC3 Q @-}
{-@ predicate CyclicC2 Q = CyclicC1 Q @-}
{-@ predicate CyclicC3 Q = CyclicC1 Q @-}

