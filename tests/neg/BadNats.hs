module Nats where

{-@ poo :: {v:Int | v == 0 } @-}
poo :: Int 
poo = 1

data Peano = Z | O 

bob :: String 
bob = "I am a cat"

{-@ axiomatize one @-}
one :: Peano 
one = O 

{-@ axiomatize zero @-}
zero :: Peano
zero = Z
