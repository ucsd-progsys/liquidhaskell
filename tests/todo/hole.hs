module Foo where

data List a = N | C a (List a)

{-@ data List a <p :: a -> a -> Prop> 
     = N | C {x :: a, xs :: List<p> a<p x>} @-}


infixr 9 `C`

nil :: List a 
nil = N
