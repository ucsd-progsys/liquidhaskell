module Sum where

{-@ LIQUID "--no-termination" @-}

{-@ ssum :: forall<p :: a -> Prop, q :: a -> Prop>. 
            {{v:a | v == 0} <: a<q>}
            {x::a<p> |- {v:a | x <= v} <: a<q>}
            [{v:a<p> | 0 <= v}] -> {v:a<q> | 0 <= v } @-}
ssum :: Num a => [a] -> a
ssum [] = 0
ssum [x] = x
ssum (x:xs) = x + ssum xs