module T1096_Foo where

import T1096_Types 

{-@ foo  :: f:Foo -> Foo / [size f] @-}
foo  :: Foo -> Foo
foo (A x) = A (foo x)
foo x     = x 
