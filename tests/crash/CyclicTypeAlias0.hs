module Test0 () where

{-@ type CyclicA1 = CyclicA2 @-}
{-@ type CyclicA2 = CyclicA1 @-}

