module StateMonad () where

type State = Int
data ST a = S (State -> (a, State))
{-@ data ST a <p1 :: State -> Prop,
               p2 :: State -> Prop> 
     = S (x::(f:State<p1> -> (a, State<p2>))) 
  @-}

{-@ fresh :: ST <{\v -> v>=0}, {\v -> v>=0}> Int @-}
fresh :: ST Int
fresh = S $ \n -> (n, n-1)


