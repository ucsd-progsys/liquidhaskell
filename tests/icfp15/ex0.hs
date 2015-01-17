module Ex0 where

import RIO

{-@ app :: forall <pre :: World -> Prop, post :: World -> a -> World -> Prop>.
           (a -> RIO <pre, post> b) -> a -> RIO <pre, post> b @-}
app :: (a -> RIO b) -> a -> RIO b
app f x = f x


{-@ 
twice  :: forall < pre   :: World -> Prop 
                 , post1 :: World -> a -> World -> Prop
                 , post :: World -> a -> World -> Prop>.
       {w:World<pre> -> x:a -> World<post1 w x> -> World<pre>}        
       {w:World<pre> -> y:a -> w2:World<post1 w y> -> x:a -> World<post1 w2 x> -> World<post w x>}        
       (b -> RIO <pre, post1> a) -> b   
    -> RIO <pre, post> a 
@-}
twice :: (b -> RIO a) -> b -> RIO a
twice f x = do {f x ; f x}


{-@ measure counter :: World -> Int @-}

{-@ incr :: RIO <{\x -> counter x >= 0}, {\w1 x w2 -> counter w2 = counter w1 + 1}>  Nat Nat @-}
incr :: RIO Int
incr = undefined

{-@ incr2 :: RIO <{\x -> counter x >= 0}, {\w1 x w2 -> counter w2 = counter w1 + 2}>  Nat Nat @-}
incr2 :: RIO Int
incr2 = twice (\_ -> incr) 0

{-@ LIQUID "--no-termination" @-}


{-@ 
while  :: forall < pre   :: World -> Prop 
                 , post1 :: World -> () -> World -> Prop
                 , post :: World -> () -> World -> Prop>.
       {w:World<pre> -> x:() -> {v:World | v = w} -> World<post w x>}
       {w:World<pre> -> x:() -> World<post1 w x> -> World<pre>}        
       {w:World<pre> -> y:() -> w2:World<post1 w y> -> x:() -> World<post w2 x> -> World<post w x>}        
       Bool -> (b -> RIO <pre, post1> ()) -> b   
    -> RIO <pre, post> () 
@-}
while :: Bool -> (b -> RIO ()) -> b -> RIO ()
while guard f x = if guard then do {f x; while guard f x} else return ()




