module HoleCrash1 where

data Poo a = C { t :: Poo a }

{-@ type Geq N = {v:_ | N <= v} @-}

{-@ data Poo a = C { t :: Poo (Geq 0) } @-}
