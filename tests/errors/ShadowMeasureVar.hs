-- REJECT this program as the measure has the same name as another binder.

module Shadow where

data Poo = Poo Int

{-@ measure shadow :: Poo -> Int
    shadow (Poo n) = n
  @-}

{-@ test :: p:Poo -> {v:Int | v = shadow p} @-}
test :: Poo -> Int
test (Poo n) = n

shadow :: Int
shadow = 121

