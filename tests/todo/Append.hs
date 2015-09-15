module Append where



data RGRef a

{-@ measure tv :: RGRef a -> a @-}
{-@ qualif FOO(r:RGRef a): ( N == 0 ) @-}

{- LIQUID "--no-termination" @-}

data L a = N

{- measure append :: L a -> L a -> L a @-}

{- axiom_nil :: xs:L a ->  {v:L a | v == xs &&  append N v == v} @-}
axiom_nil :: L a ->  L a
axiom_nil xs = xs


