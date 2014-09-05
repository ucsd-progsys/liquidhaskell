module ListDemo where

data Poo a = C { t :: Poo a }

{-@ type Geq a N = {v:a | N <= v} @-}

{-@ data Poo a = C { t :: Poo (Geq 0) } @-}
