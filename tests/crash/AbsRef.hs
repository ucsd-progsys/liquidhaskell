module Fixme where


bar :: a -> b -> a
{-@ bar :: forall<p :: a -> b -> Prop>. x:a -> b<p> -> a @-}
bar x y = x
