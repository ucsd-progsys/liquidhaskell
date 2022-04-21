{-@ LIQUID "--reflection" @-}

module T1547 where

{-@ myfst :: () -> {v:((a,b) -> a) | v == fst } @-}
myfst :: () -> (a,b) -> a 
myfst _ = fst 
