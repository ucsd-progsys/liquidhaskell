module Test1 () where

{-@ type CyclicB1 = CyclicB2 @-}
{-@ type CyclicB2 = CyclicB3 @-}
{-@ type CyclicB3 = CyclicB1 @-}

