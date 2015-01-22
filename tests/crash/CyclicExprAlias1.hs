module Test2 () where

{-@ expression CyclicB1 Q = CyclicB2 Q @-}
{-@ expression CyclicB2 Q = CyclicB1 Q @-}

