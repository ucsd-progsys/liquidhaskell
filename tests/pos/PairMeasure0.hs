module Foo where

{-@ measure fst :: (a, b) -> a 
    fst (x, y) = x
  @-}


{-@ foo :: p:(a, b) -> {v:a | (v = (fst p))} @-}
foo (x, y) = x

