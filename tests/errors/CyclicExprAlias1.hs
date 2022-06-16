{-@ LIQUID "--expect-error-containing=Cyclic type alias definition" @-}
module CyclicExprAlias1 () where

{-@ expression CyclicB1 Q = CyclicB2 Q @-}
{-@ expression CyclicB2 Q = CyclicB1 Q @-}

