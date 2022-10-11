{-@ LIQUID "--expect-error-containing=Cyclic type alias definition for `CyclicB1`" @-}
module CyclicPredAlias1 () where

{-@ predicate CyclicB1 Q = CyclicB2 Q @-}
{-@ predicate CyclicB2 Q = CyclicB1 Q @-}

