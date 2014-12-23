module Compose where




data ST s a = ST {runState :: s -> s}

{-@ data ST s a <p :: s -> Prop, q :: s -> s -> Prop> = ST (runState :: x:s<p> -> s<q x>) @-}




{-@ 
cmp :: forall < pref :: s -> Prop, postf :: s -> s -> Prop
              , pre  :: s -> Prop, postg :: s -> s -> Prop
              , post :: s -> s -> Prop
              >. 
       {y:s -> s<postg y> -> s<pref>}
       {x:s<pre> -> z:s<postg x> -> s<postf z> -> s<post x> }
       f:(ST <pref, postf> s a)
    -> g:(ST <pre , postg> s b)
    ->   (ST <pre , post > s b)
@-}

cmp :: ST s a
    -> ST s b
    -> ST s b

cmp (ST f) (ST g) = ST $ \s -> f (g s)


{-@ incr :: ST <{\x -> x >= 0}, {\x v -> v = x + 1}> Nat Int @-}
incr :: ST Int Int 
incr = ST $ \x -> x + 1

{-@ incr2 :: ST <{\x -> x >= 0}, {\x v -> v = x + 4}> Nat Int @-}
incr2 :: ST Int Int 
incr2 = cmp incr incr




































