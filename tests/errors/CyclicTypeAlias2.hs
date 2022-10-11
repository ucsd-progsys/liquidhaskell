{-@ LIQUID "--expect-error-containing=Cyclic type alias definition for `CyclicC`" @-}
module CyclicTypeAlias2 () where

{-@ type CyclicC = [CyclicC] @-}

