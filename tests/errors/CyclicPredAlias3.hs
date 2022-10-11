{-@ LIQUID "--expect-error-containing=Cyclic type alias definition for `CyclicD1`" @-}
module CyclicPredAlias3 () where

{-@ predicate CyclicD1 Q = CyclicD2 Q @-}
{-@ predicate CyclicD2 Q = CyclicD3 Q @-}
{-@ predicate CyclicD3 Q = CyclicD1 Q @-}

