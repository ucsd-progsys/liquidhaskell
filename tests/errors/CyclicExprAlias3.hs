module Test3 () where

{-@ expression CyclicD1 Q = CyclicD2 Q @-}
{-@ expression CyclicD2 Q = CyclicD3 Q @-}
{-@ expression CyclicD3 Q = CyclicD1 Q @-}

