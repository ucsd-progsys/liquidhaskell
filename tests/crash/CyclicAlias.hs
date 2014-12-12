module Test0 () where

{-@ type CyclicA1 = CyclicA2 @-}
{-@ type CyclicA2 = CyclicA1 @-}

{-@ type CyclicB1 = CyclicB2 @-}
{-@ type CyclicB2 = CyclicB3 @-}
{-@ type CyclicB3 = CyclicB1 @-}

{-@ type CyclicC = [CyclicC] @-}

{-@ type CyclicD1 = CyclicD2 @-}
{-@ type CyclicD2 = CyclicD3 @-}
{-@ type CyclicD3 = CyclicD2 @-}

