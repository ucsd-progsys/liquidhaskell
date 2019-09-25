{-@ LIQUID "--reflection" @-}

module Foo where

{-@ myfst :: () -> {v:((a,b) -> a) | v == fst } @-}
myfst :: () -> (a,b) -> a 
myfst _ = fst 