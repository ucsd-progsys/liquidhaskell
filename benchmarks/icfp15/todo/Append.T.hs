module Compose where

{-@ app :: forall <p :: a -> Prop, q :: a -> Prop, w :: a -> a -> Prop>.
        {x::a<p> |- a<q> <: a<w x>}
        [a<p>]<w> -> [a<q>]<w> -> [a]<w> @-}
app []      ys = ys
app (x:xs) ys = x:(xs `app` ys)

