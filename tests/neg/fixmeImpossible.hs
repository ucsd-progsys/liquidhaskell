module Fixme where

data F a = L a 

{-@ foo :: a -> F a b -> F a @-}
foo :: a -> F a -> F a
foo = undefined


