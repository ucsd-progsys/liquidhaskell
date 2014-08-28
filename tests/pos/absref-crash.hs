module Foo where

data L a = C (L a)

{-@ data L a <p :: L a -> Prop> = C { xs :: L<p> a } @-}

foo :: b -> L a
foo x = C $ foo x
