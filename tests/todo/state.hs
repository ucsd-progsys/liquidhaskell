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

-- The above does is not Safe, because s' is not visible 
-- in the type signature
-- The same pattern exists in function composition:
-- What can we have in the result?

{- foo :: forall <p :: xx:a -> a -> Prop>.
     (x:a -> a<p x>) -> g:(x:a -> a<p x>) -> y:a -> 
      a<p ?? >
 @-}
foo :: (a -> a) -> (a -> a) -> a -> a
foo f g x =
  let s' = g x in f s'

-- We can not have exists [j:{v:a | v = (g x)}]




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
       



