{-
  A first example in equalional reasoning. 
  From the definition of append we should be able to 
  semi-automatically prove the three axioms.
 -}

{-@ LIQUID "--newcheck" @-}
{-@ LIQUID "--no-termination" @-}

module Append where

data L a = N |  C a (L a) deriving (Eq)

{-@ measure append :: L a -> L a -> L a @-}
append :: L a -> L a -> L a 
append N xs        = xs
append (C y ys) xs = C y (append ys xs) 


{-@ type Valid = {v:Bool | Prop v <=> true } @-}

{-@ prop_nil_left :: xs:L a -> Valid @-}
prop_nil_left     :: Eq a => L a -> Bool
prop_nil_left xs = let tmp1 = append N xs in 
                   let tmp2 = axiom_nil_left tmp1 in 
                   tmp2 == xs


{-@ assume axiom_nil_left :: xs:L a ->  {v:L a | v == xs &&  append N v == v} @-}
axiom_nil_left :: L a ->  L a
axiom_nil_left xs = xs


{- axiom_nil_right :: xs:L a ->  {v:L a | v == xs &&  append v N == v} @-}
axiom_nil_right :: L a ->  L a
axiom_nil_right xs = xs


{- axiom_assoc :: xs:L a -> ys: L a ->  zs: L a -> {v: Bool | append xs (append ys zs) == append (append xs ys) zs } @-}
axiom_assoc :: L a ->  L a -> L a -> Bool 
axiom_assoc xs ys zs = True 
