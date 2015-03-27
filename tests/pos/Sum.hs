module Sum where

{-@ ssum :: forall<p :: a -> Prop, q :: a -> Prop>. 
            {{v:a | v == 0} <: a<q>}
            {x::a<p> |- {v:a | x <= v} <: a<q>}
            xs:[{v:a<p> | 0 <= v}] -> {v:a<q> | len xs >= 0 && 0 <= v } @-}
ssum :: Num a => [a] -> a
ssum []       = 0
ssum [x]      = x
ssum (x:xs)   = x + ssum xs