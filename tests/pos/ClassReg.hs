module Compose where


data ST s a = ST {runState :: s -> (a,s)}

{-@ data ST s b <r :: s -> b -> Prop> 
  = ST (runState :: x:s -> (b<r x>, s)) @-}


class MM m where
  bind :: m a -> (a -> m b) -> m b
  cmp  :: m a -> m b -> m b

instance MM (ST s) where
  cmp m f = bind m (\_ -> f) 


 
