module State where

import Prelude hiding (snd, fst)

data ST a s = S (s -> (a, s))
{-@ data ST a s <pre :: s -> Prop, post :: a -> s -> Prop> 
       = S (ys::(x:s<pre> -> ((a, s)<post>)))
  @-}

{-@ return :: forall <pre :: s -> Prop, post :: a -> s -> Prop>.
               x:a 
           -> ST <{v:s<post x>| true}, post> a s
  @-}
return :: a -> ST a s
return x = S $ \s -> (x, s)


{-@ bind :: forall <p :: s -> Prop, q :: a -> s -> Prop, r :: b -> s -> Prop>.
            ST <p, q> a s 
         -> (x:a -> ST <{v:s<q x> | true}, r> b s) 
         -> ST <p, r> b s
 @-}
bind :: ST a s -> (a -> ST b s) -> ST b s
bind (S m) k = S $ \s -> let (a, s') = m s in apply (k a) s'

{-@ apply :: forall <p :: s -> Prop, q :: a -> s -> Prop>.
             ST <p, q> a s -> s<p> -> (a, s)<q>
  @-}
apply :: ST a s -> s -> (a, s)
apply (S f) s = f s
