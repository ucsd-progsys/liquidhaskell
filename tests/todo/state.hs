module StateMonad where

type State = Int
data ST a = S (State -> (a, State))
{-@ data ST a <p1 :: old:State -> State -> Prop,
               p2 :: old:State -> a -> Prop> 
     = S (x::(f:State -> (a<p2 f>, State<p1 f>))) 
  @-}

{-@ type IState a = (ST a) <\f->{v:State |v=f}, \f->{v:a|v=f+1}>@-}

-- apply0 :: ST a -> State -> (a, State)


{-@
apply0 :: forall a <p1 :: old:State -> State -> Prop, 
                    p2 :: old:State -> a -> Prop>.
          (ST a) <p1, p2> -> f:State -> (a<p2 f>, State<p1 f>)
  @-}
apply0 :: ST a -> State -> (a, State)
apply0 (S f) x = f x

-- fresh :: ST Int
{- fresh :: n:Int -> ({v:Int|v=n}, {v:Int|v=n+1})@-}
{-@ fresh :: IState State @-}
fresh = S (\n -> (n, n+1))



-- foo 0 = return []
-- 
-- foo n = do x <- foo 
--            xs <- foo $ n-1
--            return $ x :xs
-- 
       


{-@ foo :: ({v:Int|v>=0}, Int) @-}
foo :: (Int, Int)
foo = apply0 fresh 0
