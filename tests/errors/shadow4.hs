-- ISSUE: Currently this doesn't CRASH because the two sorts for `unPoo` are the
-- same, but that is a happy coincidence. We should REJECT this program as the
-- measure has the same name as another binder.

module Shadow where

data Poo = Poo Int

{-@ measure unPoo :: Poo -> Int
    unPoo (Poo n) = n
  @-}

{-@ test :: p:Poo -> {v:Int | v = unPoo p} @-}
test :: Poo -> Int
test (Poo n) = n

{-@ measure unPoo @-}
unPoo :: Poo -> Int
unPoo (Poo z) = 121

{-@ measure zink @-}
zink :: Poo -> Int
zink (Poo n) = n

{-@ reflect hup @-}
hup :: Poo -> Int
hup (Poo n) = n
