{-@ LIQUID "--expect-error-containing=Cyclic type alias definition for `CyclicA1`" @-}
module CyclicTypeAlias0 () where

{-@ type CyclicA1 = CyclicA2 @-}
{-@ type CyclicA2 = CyclicA1 @-}

