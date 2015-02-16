module TwiceM where

import RIO

{-@ app :: forall <pre :: World -> Prop, post :: World -> b -> World -> Prop, p :: b -> Prop>.
           (a -> RIO <pre, post, p> b) -> a -> RIO <pre, post, p> b @-}
app :: (a -> RIO b) -> a -> RIO b
app f x = f x


{-@
twice  :: forall < pre   :: World -> Prop 
                 , post1 :: World -> a -> World -> Prop
                 , post :: World -> a -> World -> Prop
                 , p :: a -> Prop>.
                 {w::World<pre> , x::a|- World<post1 w x> <: World<pre>}
       (b -> RIO <pre, post1, p> a)  
     -> b -> RIO <pre, post, p> a 
@-}
twice :: (b -> RIO a) -> b -> RIO a
twice f x = f x >> f x


{- measure counter :: World -> Int @-}

{- incr :: RIO <{\x -> counter x >= 0}, {\w1 x w2 -> counter w2 = counter w1 + 1}>  Nat Nat @-}
incr :: RIO Int
incr = undefined

{- incr2 :: RIO <{\x -> counter x >= 0}, {\w1 x w2 -> counter w2 = counter w1 + 2}>  Nat Nat @-}
incr2 :: RIO Int
incr2 = twice (\_ -> incr) 0