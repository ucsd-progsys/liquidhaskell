{-@ LIQUID "--expect-error-containing=Malformed application of type alias `Geq`" @-}
module HoleCrash2 where

data Poo a = C { t :: Poo a }

{-@ type Geq a N = {v:a | N <= v} @-}

{-@ data Poo a = C { t :: Poo (Geq 0) } @-}
