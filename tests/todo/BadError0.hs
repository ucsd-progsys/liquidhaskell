module Foo where


data F a = F a
{-@ data F a <p :: a -> Prop> = F {x::a} @-}

{-@ foo :: forall<p :: a -> Prop>. (a -> F <p> b) -> a -> F <p> b @-}
foo :: (a -> F b) -> a -> F b
foo f x = f x 