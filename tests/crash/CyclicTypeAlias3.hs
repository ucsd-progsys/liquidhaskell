module Test3 () where

{-@ type CyclicD1 = CyclicD2 @-}
{-@ type CyclicD2 = CyclicD3 @-}
{-@ type CyclicD3 = CyclicD2 @-}

