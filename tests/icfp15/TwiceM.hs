module TwiceM where

{-@ LIQUID "--short-names" @-}

import RIO

{-@ appM :: forall <pre :: World -> Prop, post :: World -> b -> World -> Prop, p :: b -> Prop>.
           (a -> RIO <pre, post, p> b) -> a -> RIO <pre, post, p> b @-}
appM :: (a -> RIO b) -> a -> RIO b
appM f x = f x


{-@
twiceM  :: forall < pre   :: World -> Prop 
                 , post1 :: World -> a -> World -> Prop
                 , post :: World -> a -> World -> Prop
                 , p :: a -> Prop>.
                 {w ::World<pre>, x::a|- World<post1 w x> <: World<pre>}
                 {w1::World<pre>, y::a, w2::World<post1 w1 y>, w20::{v:World<pre> | v = w2}, x::a |- World<post1 w2 x> <: World<post w1 x>}
       (b -> RIO <pre, post1, p> a)  
     -> b -> RIO <pre, post, p> a 
@-}
twiceM :: (b -> RIO a) -> b -> RIO a
twiceM f w = let (RIO g) = f w in RIO $ \x -> case g x of {(y, s) -> let ff = \_ -> f w in (runState (ff y)) s} 


{-@ measure counter :: World -> Int @-}

{-@ incr :: RIO <{\x -> counter x >= 0}, {\w1 x w2 -> counter w2 = counter w1 + 1}, {\x -> true}>  Nat Nat @-}
incr :: RIO Int
incr = undefined

{-@ incr2 :: RIO <{\x -> counter x >= 0}, {\w1 x w2 -> counter w2 = counter w1 + 2}, {\x -> true}> Nat Nat @-}
incr2 :: RIO Int
incr2 = twiceM (\_ -> incr) 0
