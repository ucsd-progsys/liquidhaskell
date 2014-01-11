module Foo () where

{-@ foo :: p:(a, b) -> {v:a | (v = (fst p))} @-}
foo (x, y) = x

