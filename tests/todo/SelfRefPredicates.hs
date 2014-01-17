module Fixme where

{-@ bindST :: forall <p :: s -> Prop, q :: s -> a -> s -> Prop, r :: s -> b -> s -> Prop>.
            (xm:s<p> -> (a, s)<q xm>) 
         -> (xbind:a ->  xk:(exists[xxxa:a].exists[xxa:s<p>].s<q xxa xxxa>) -> (b, s)<r xk>) 
         -> xr:s<p> -> exists[xa:a]. exists[xxx:s<q xr xa>]. (b, s)<r xxx>
 @-}
bindST :: (s -> (a, s)) -> (a -> (s -> (b, s))) -> (s ->  (b, s))
bindST m k s =  let (a, s') = m s in (k a) s'



{-@ returnST :: forall <p :: s -> a -> s -> Prop>.
                   xa:a -> xs:s<p v xa> -> (a,s)<p xs> @-}
returnST :: a -> s -> (a, s)
returnST x s = (x, s) 
