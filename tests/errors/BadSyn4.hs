module Foo where

type List a = [a]
type Point  = List Double

{-@ foo :: n:Nat -> Point n @-}
foo :: Int -> List Double
foo _ = []
