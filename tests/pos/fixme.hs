module Foo where

data F = F { foo :: Int}

{-@ data F <p :: Int -> Prop> = F (i :: Int<p>)@-}

{-@ foo  :: F -> {v:Int| v = 0} @-}
