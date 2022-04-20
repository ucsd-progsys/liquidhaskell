{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

module Tmp1 where

data Peano = Zero | Succ Peano 

{-@ reflect ev @-}
ev :: Peano -> Bool 
ev Zero     = True 
ev (Succ n) = not (ev n)

{-@ goo :: n:_ -> {b:Bool | b = ev n} @-}
goo :: Peano -> Bool 
goo Zero     = True 
goo (Succ n) = case n of 
                 Succ Zero -> True
                 _         -> undefined
