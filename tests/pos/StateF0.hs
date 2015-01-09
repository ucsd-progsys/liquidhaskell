module State (
   returnST -- :: a -> ST a s
 , bindST   -- :: ST a s -> (a -> ST b s) -> ST b s
 , ST(..)
 ) where

import Prelude hiding (snd, fst)

data ST a s = S (s -> (a, s))
{-@ data ST a s <pre :: s -> Prop, post :: s -> a -> s -> Prop> 
       = S (ys::(x:s<pre> -> ((a, s)<\xx -> {v:s<post x xx> | true}>)))
  @-}


{-@ returnF :: forall < pre :: s -> Prop>.
               xState:a 
            -> sState:s<pre> ->  (a,s)<{\x v -> ((v = sState) && (x = xState))}> 
  @-}
returnF :: a -> s -> (a, s)
returnF x = \s -> (x, s)

{- returnST :: forall < pre :: s -> Prop>.
               xState:a 
            -> ST <pre, {\xs xa v -> ((v = xs) && (xState = xa))}> a s 
  @-}

returnST :: a -> ST a s
returnST x = S $ \s -> (x, s)

{-@ bindF0 :: forall < p :: s -> Prop
                     , w :: b -> s -> Prop
                     , q :: s -> a -> s -> Prop
                     , r :: s -> b -> s -> Prop>.
            (xm:s<p> -> (a, s)<\xx -> {v:s<q xm xx> | true}>) 
         -> (xbind:a -> xk:s -> (b, s)<\xx -> {v:s<r xk xx> | true}>) 
         -> (xr:s<p> -> exists[xa:a].exists[xs:s<q xr xa>].(b, s)<\xx -> {v:s<r xs xx> | true}>)
 @-}
bindF0 :: (s -> (a, s)) -> (a -> (s -> (b, s))) -> (s -> (b, s))
bindF0 m k = \s -> let (a, s') = m s in (k a) s'

-- STEP 1: reorder s to give pass predondition

{-@ bindF1 :: forall < p :: s -> Prop
                    , w :: b -> s -> Prop
                    , q :: s -> a -> s -> Prop
                    , r :: s -> b -> s -> Prop>.
            (xm:s<p> -> (a, s)<\xx -> {v:s<q xm xx> | true}>) 
         -> xr:s<p>
         -> (xbind:a -> xk:(exists[xa:a]. s<q xr xa>) -> (b, s)<\xx -> {v:s<r xk xx> | true}>) 
         -> ( exists[xa:a].exists[xs:s<q xr xa>].(b, s)<\xx -> {v:s<r xs xx> | true}>)
 @-}
bindF1 :: (s -> (a, s)) -> s ->  (a -> (s -> (b, s))) -> ((b, s))
bindF1 m s k = let (a, s') = m s in (k a) s'




{- bindST :: forall < p :: s -> Prop
                    , q :: s -> a -> s -> Prop
                    , r :: s -> b -> s -> Prop>.
            ST<p, q> a s
         -> (xbind:a -> ST<true, r> b s) 
         -> (xr:s<p> -> exists[xa:a].exists[xs:s<q xr xa>].(b, s)<r xs>)
 @-}
bindST :: ST a s -> (a -> ST b s) -> ST b s
bindST (S m) k = S $ \s -> let (a, s') = m s in applyST (k a) s'

{- apply :: forall <p :: s -> Prop, q :: s -> a -> s -> Prop>.
             ST <p, q> a s -> x:s<p> -> (a, s)<q x>
  @-}
applyST :: ST a s -> s -> (a, s)
applyST (S f) s = f s
