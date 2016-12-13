module State (
   returnST -- :: a -> ST a s
 , bindST   -- :: ST a s -> (a -> ST b s) -> ST b s
 , ST(..)
 ) where

import Prelude hiding (snd, fst)

data ST a s = S (s -> (a, s))
{-@ data ST a s <pre :: s -> Bool, post :: a -> s -> Bool> 
       = S (ys::(x:s<pre> -> ((a, s)<post>)))
  @-}

{-@ returnST :: forall <pre :: s -> Bool, post :: a -> s -> Bool>.
               xState:a 
           -> ST <{v:s<post xState>| true}, post> a s
  @-}
returnST :: a -> ST a s
returnST x = S $ \s -> (x, s)


{-@ bindST :: forall <pbind :: s -> Bool, qbind :: a -> s -> Bool, rbind :: b -> s -> Bool>.
            ST <pbind, qbind> a s 
         -> (xbind:a -> ST <{v:s<qbind xbind> | true}, rbind> b s) 
         -> ST <pbind, rbind> b s
 @-}
bindST :: ST a s -> (a -> ST b s) -> ST b s
bindST (S m) k = S $ \s -> let (a, s') = m s in apply (k a) s'

{-@ apply :: forall <p :: s -> Bool, q :: a -> s -> Bool>.
             ST <p, q> a s -> s<p> -> (a, s)<q>
  @-}
apply :: ST a s -> s -> (a, s)
apply (S f) s = f s
