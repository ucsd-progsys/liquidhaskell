module Compose where




data ST s = ST {runState :: s -> s}

{-@ data ST s t <p :: s -> Prop, q :: s -> s -> Prop> = ST (runState :: x:s<p> -> s<q x>) @-}

 {-@ runState :: forall <p :: s -> Prop, q :: s -> s -> Prop>. ST <p, q> s -> x:s<p> -> s<q x> @-}



{-@ 
cmp :: forall < pref :: s -> Prop, postf :: s -> s -> Prop
              , pre  :: s -> Prop, postg :: s -> s -> Prop
              , post :: s -> s -> Prop
              >. 
       {xx:s<pre> -> w:s<postg xx> -> s<postf w> -> s<post xx>}
       {ww:s<pre> -> s<postg ww> -> s<pref>}
       (ST <pref, postf> s)
    -> (ST <pre, postg> s)
    -> (ST <pre, post> s)
@-}

cmp :: (ST s)
    -> (ST s)
    -> (ST s)

cmp (ST f) (ST g) = ST (\x -> f (g x))    



{-@ incr :: ST <{\x -> x >= 0}, {\x v -> v = x + 1}>  Nat   @-}
incr :: ST Int 
incr = ST $ \x ->  x + 1


{-@ incr2 :: ST <{\x -> x >= 0}, {\x v -> v = x + 5}>  Nat  @-}
incr2 :: ST Int 
incr2 = cmp incr incr

{-@ incr3 :: ST <{\x -> x >= 0}, {\x v -> v = x + 4}>  Nat  @-}
incr3 :: ST Int 
incr3 = cmp (cmp incr incr) incr


foo :: Int
{-@ foo :: {v:Nat |  v = 10} @-}
foo = (runState incr3) 0





































