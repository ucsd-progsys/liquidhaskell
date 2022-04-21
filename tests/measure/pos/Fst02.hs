-- TAG: measure 
-- test if the "builtin" fst and snd measures work.

module Fst02 where

{- assume Data.Tuple.fst :: x:(a,b) -> {v:a | v = fst x} @-}

{-@ foo :: z:_ -> {v:_ | v = fst z} @-}  
foo :: (a, b) -> a 
foo z = fst z 

