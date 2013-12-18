module State (
   returnST -- :: a -> ST a s
 , bindST   -- :: ST a s -> (a -> ST b s) -> ST b s
 , ST(..)
 ) where

import Prelude hiding (snd, fst)

data ST a s = S (s -> (a, s))
{-@ data ST a s <pre :: s -> Prop, post :: a -> s -> Prop> 
       = S (ys::(x:s<pre> -> ((a, s)<post>)))
  @-}

{-@ returnST :: forall <pre :: s -> Prop, post :: a -> s -> Prop>.
               xState:a 
           -> ST <{v:s<post xState>| true}, post> a s
  @-}
returnST :: a -> ST a s
returnST x = S $ \s -> (x, s)


{-@ bindST :: forall <p :: s -> Prop, q :: a -> s -> Prop, r :: b -> s -> Prop>.
            ST <p, q> a s 
         -> (xbind:a -> ST <{v:s<q xbind> | true}, r> b s) 
         -> ST <p, r> b s
 @-}
bindST :: ST a s -> (a -> ST b s) -> ST b s
bindST (S m) k = S $ \s -> let (a, s') = m s in apply (k a) s'

{-@ apply :: forall <p :: s -> Prop, q :: a -> s -> Prop>.
             ST <p, q> a s -> s<p> -> (a, s)<q>
  @-}
apply :: ST a s -> s -> (a, s)
apply (S f) s = f s
