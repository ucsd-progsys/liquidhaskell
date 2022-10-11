{-@ LIQUID "--expect-error-containing=Multiple specifications for `shadow`" @-}

-- ISSUE: Currently this doesn't CRASH because the two sorts for `shadow` are the
-- same, but that is a happy coincidence. We should REJECT this program as the
-- measure has the same name as another binder.

module ShadowMeasure where

data Poo = Poo Int

{-@ measure shadow :: Poo -> Int
      shadow (Poo n) = n
  @-}

{-@ test :: p:Poo -> {v:Int | v = shadow p} @-}
test :: Poo -> Int
test (Poo n) = n

{-@ measure shadow @-}
shadow :: [a] -> Int
shadow [] = 0
shadow (x:xs) = 0
