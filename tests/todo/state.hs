module StateMonad where

data ST s a = S (s -> (a, s))

{-@ data ST s a <p1 :: old:s -> s -> Prop>
     = S (x::(f:s -> (a, s<p1 f>))) 
  @-}

{-@
apply :: forall s a <p1 :: old:s -> s -> Prop>.
          ST <p1> s a-> f:s -> (a, s<p1 f>)
  @-}
apply :: ST s a -> s -> (a, s)
apply (S f) x = f x



-- TODO >>= does not parse...
{-@
seq :: forall <p1 :: old:s -> s -> Prop>.
        ST <p1> s a -> (a ->  ST <p1> s b) -> ST <p1> s b
  @-}
seq :: ST s a -> (a -> ST s b) -> ST s b
m `seq` k = S $ \s -> 
  let (a, s') = apply m s in apply (k a) s'

-- The above test is UNSAFE becase it requires
-- the S :: x:s -> exists[y:s<p1 x>]. (a, s<p1 y>)
--
{-
seq' :: forall <p1 :: old:s -> s -> Prop>.
        ST <p1> s a -> (a ->  ST <p1> s b) -> 
        x:s -> exists[y:s<p1 x>]. (a, s<p1 y>)
  @-}
-- seq' :: ST s a -> (a -> ST s b) -> ST s b
-- m `seq'` k = S $ \s -> 
--   let (a, s') = apply m s in apply (k a) s'


{-@ fresh :: ST <\st -> {v:Int|v=st+1}> Int Int@-}
fresh :: ST Int Int
fresh = S (\n -> (n, n+1))

{-@ bar :: (Int, {v:Int|v>=0}) @-}
bar :: (Int, Int)
bar = apply fresh 0

-- foo 0 = return []
-- 
-- foo n = do x <- foo 
--            xs <- foo $ n-1
--            return $ x :xs
-- 
       



