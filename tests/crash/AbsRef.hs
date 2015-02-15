module Fixme where


foo :: [a] -> ()
{-@ foo :: [{v:a | v = 5}] -> () @-}
foo _ = ()


bar :: a -> b -> a
{-@ bar :: forall<p :: a -> b -> Prop>. x:a -> {xx:b<p> | xx > xx} -> a @-}
bar x y = x
