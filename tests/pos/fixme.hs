module Foo where

data F a = F a

-- give F two parameters instead of one
{-@ foo :: a -> F a b @-} 
foo :: a -> F a
foo = undefined
