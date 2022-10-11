{-@ LIQUID "--expect-any-error" @-}
-- TAG: measure 
-- test if the "builtin" fst and snd measures work.

module Fst02 where

{-@ foo :: z:_ -> {v:_ | v = snd z} @-}  
foo :: (a, a) -> a 
foo z = fst z 

