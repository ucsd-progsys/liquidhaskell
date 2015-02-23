module Reverse where


--   Sym p q  == x:a, y:a<p x> |- { v:a | v = x} <: a<q y>

{- rgo :: (Sym p q) => x:a -> [a<q x>]<q> -> [a<p x>]<p> -> [a]<q> @-}

{-@ rev ::  forall <p :: a -> a -> Prop, q :: a -> a -> Prop, q1 :: a -> a -> Prop>.
  {x::a, y::a<p x> |- {v:a|v=x} <: a<q y>}
  x:a -> [a<p x>]<p> -> [a<q x>]<q> ->[a]<q> @-}
rev :: a -> [a] -> [a] -> [a]
rev z []     a = z:a
rev z (x:xs) (ax:axs) = x : ax : [] -- a -- rev x xs (z:a)

-- x :: p z 
-- a :: 