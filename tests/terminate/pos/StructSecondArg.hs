
module StructSecondArg where

data Peano = Z | S Peano

addToInt :: Int -> Peano -> Int
addToInt n Z     = n
addToInt n (S p) = addToInt (n + 1) p
