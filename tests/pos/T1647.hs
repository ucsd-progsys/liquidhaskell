{-# LANGUAGE GADTs        #-}
{-@ LIQUID "--reflection" @-} 

module T1647 where

{-@ type ExtTR a E1 E2 = {v:ExtT a | E1 == E2 } @-}

data ExtT b  where 
   ExtT  :: (a -> b) -> ExtT b 

{-@ data ExtT b where 
      ExtT  :: (a -> b) -> ExtT b 
@-}   

prop :: a -> a -> ExtT a -> ExtT a
{-@ prop :: x:a -> y:a-> ExtTR a {x} {y} -> ExtTR a {x} {y} @-}
prop f g (ExtT ctx) = ExtT ctx   
