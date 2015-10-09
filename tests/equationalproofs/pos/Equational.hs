module Equational where


import Language.Haskell.Liquid.Prelude
import Axiomatize


{-@ toProof :: l:a -> r:{a | l == r} -> {v:Proof | l == r } @-}
toProof :: a -> a -> Proof
toProof x y = Proof


{-@ (===) :: l:a -> r:a -> {v:Proof | l = r} -> {v:a | v = l } @-}
(===) :: a -> a -> Proof -> a
(===) x y _ = y



{-@ type Equal X Y = {v:Proof | X == Y} @-}

{-@ bound chain @-}
chain :: (Proof -> Bool) -> (Proof -> Bool) -> (Proof -> Bool)
      -> Proof -> Proof -> Proof -> Bool
chain p q r = \v1 v2 v3 -> p v1 ==> q v2 ==> r v3

{-@  by :: forall <p :: Proof -> Prop, q :: Proof -> Prop, r :: Proof -> Prop>.
                 {vp::Proof<p> |- Proof<q> <: Proof<r> }
                 Proof<p> -> Proof<q> -> Proof<r>
@-}
by :: Proof -> Proof -> Proof
by _ r = r

{-@ refl :: x:a -> Equal x x @-}
refl :: a -> Proof
refl x = Proof
