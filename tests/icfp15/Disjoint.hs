-- Niki Vazou TODO : How dow we prove Disjiontness of the contra-variant domain?

module Disjoint where


{-@  disjoint ::forall <p :: a -> Prop, q :: a -> Prop>.
     {x:a<p> -> y:a<q> -> {v:a | v = x && v = y} -> {v:a|false}} 
   (a<p> -> ()) -> (a<q> -> ()) -> a 
  @-}
disjoint :: (a -> ()) -> (a -> ()) -> a
disjoint = undefined


data Tag = NAME 
         | AGE 
         | MAIL 
         | ADDRESS  
         deriving Eq


pos, nat :: Tag -> ()
{-@ pos :: {v:Tag | v = NAME || v = AGE} -> () @-}
{-@ nat :: {v:Tag | v = NAME || v = AGE || v = MAIL} -> () @-}
pos = undefined
nat = undefined

foo = disjoint pos nat