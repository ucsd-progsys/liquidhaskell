module Nats (poo) where

import Language.Haskell.Liquid.Prelude 

poo :: () 
poo = liquidAssert (alice /= bob) () 

-- && bob == charlie) ()

alice :: String 
alice = "I am a dog"

bob :: String 
bob = "I am a cat"

charlie :: String 
charlie = "I am a cat"
