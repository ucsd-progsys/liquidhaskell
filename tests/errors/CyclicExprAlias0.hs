{-@ LIQUID "--expect-error-containing=Cyclic type alias definition" @-}
module CyclicExprAlias0 () where

{-@ expression CyclicA1 Q = CyclicA1 Q @-}

