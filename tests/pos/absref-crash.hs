module Foo where

data L a = C (L a)

{-@ data L a <p :: L a -> Bool> = C { xs :: L<p> a } @-}

{-@ Lazy foo @-}
foo :: b -> L a
foo x = C $ foo x
