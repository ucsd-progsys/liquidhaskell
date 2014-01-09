module Foo () where

{-@ foo :: forall a <p :: x0:Int -> x1:a -> Prop>. 
             (i:Int -> a<p i>) -> {v:Int| v=0}
              -> a <p 0>
  @-}

foo ::  (Int -> a) -> Int ->  a
foo f i = f i

