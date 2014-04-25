module Invariant where

data F a = F {fx :: a, fy :: a, fzz :: a} | G {fx :: a}

{-@ data F a = F {fx :: a, fy :: a, fz :: a}
             | G {fx :: a} 
  @-}

{-@ fooG :: x:a -> {v : F a | (fx v) = x} @-}
fooG :: a -> F a
fooG x = G x 

{-@ foo :: x:a -> {v : F a | (fx v) = x} @-}
foo :: a -> F a
foo x = F x x x
