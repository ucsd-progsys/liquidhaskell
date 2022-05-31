{-@ LIQUID "--expect-error-containing=Cyclic type alias definition for `CyclicA1`" @-}
module CyclicPredAlias0 () where

{-@ predicate CyclicA1 Q = CyclicA1 Q @-}

