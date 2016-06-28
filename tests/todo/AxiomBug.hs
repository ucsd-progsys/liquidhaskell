module Nats where

{-@ poo :: {v:Int | v == 0 } @-}
poo :: Int 
poo = 1

data Peano = Z 

{-@ axiomatize zero @-}
zero :: Peano
zero = Z
