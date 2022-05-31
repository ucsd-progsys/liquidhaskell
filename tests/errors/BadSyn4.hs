{-@ LIQUID "--expect-error-containing=Malformed application of type alias `BadSyn4.Point`" @-}
module BadSyn4 where

type List a = [a]
type Point  = List Double

{-@ foo :: n:Nat -> Point n @-}
foo :: Int -> List Double
foo _ = []
