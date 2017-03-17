module Nats where

import Language.Haskell.Liquid.Prelude 

poo :: () 
poo = liquidAssert (zero /= one) ()

data Peano = Z | O deriving (Eq)

bob :: String 
bob = "I am a cat"

{-@ axiomatize one @-}
one :: Peano 
one = O 

{-@ axiomatize zero @-}
zero :: Peano
zero = Z
