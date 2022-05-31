{-@ LIQUID "--expect-error-containing=Cyclic type alias definition" @-}
module CyclicExprAlias2 () where

{-@ expression CyclicC1 Q = (CyclicC2 Q) && (CyclicC3 Q) @-}
{-@ expression CyclicC2 Q = CyclicC1 Q @-}
{-@ expression CyclicC3 Q = CyclicC1 Q @-}


