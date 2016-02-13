module Foo where

data List a = Empty | Cons a (List a)

{-@ data List a <p :: a -> a -> Prop> 
     = Empty | Cons {x :: a, xs :: List<p> a<p x>} @-}


nil :: List a 
nil = Empty
