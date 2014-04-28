module Foo where

{-@ qualif Foo(v:a, x:List a) : (Set_mem v (listElts xs)) @-}

{-@ foo :: Nat -> Nat @-}
foo :: Int -> Int
foo x = x

