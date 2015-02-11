module Ex1 where

import RIO

{-@ LIQUID "--no-termination" @-}



-- THIS TYPE CHECKS, BUT HOW CAN WE ACTUALLY USE IT?
{-@ 
whileM  :: forall < pre   :: World -> Prop 
                  , post1 :: World -> () -> World -> Prop
                  , post2 :: World -> Bool -> World -> Prop
                  , post :: World -> () -> World -> Prop>.
       {w::World<pre>, w2::World<pre>, x::() |- World<post1 w2 x> <: World<post w x>}             
       {w::World<pre>, x::() |- {v:World | v = w} <: World<post1 w x>}
       {w::World<pre>, x::() |- {v:World | v = w} <: World<post w x>}
       {w::World<pre>, x::(), xx::Bool |- {v:World<post w x> | Prop xx} <: World<pre>}
       {w1::World, x::Bool |- World<post2 w1 x> <: World<pre>}        
       RIO <pre, post2> Bool 
       -> RIO <pre, post1> () 
       -> RIO <pre, post> ()
@-}
whileM :: RIO Bool -> RIO () -> RIO ()
whileM guard e1 = do {g <- guard ; if g then do {e1; whileM guard e1} else return ()}


{-@ measure counter1 :: World -> Int @-}
{-@ measure counter2 :: World -> Int @-}

{-@ incr' :: RIO <{\x -> true}, {\w1 x w2 -> counter1 w2 = counter1 w1 + 1}> () @-}
incr' :: RIO ()
incr' = undefined

{-@ condM :: RIO <{\x -> true}, {\w1 x w2 -> (Prop x) <=> counter1 w2 >= counter2 w2}> Bool @-}
condM :: RIO Bool
condM = undefined

-- NV: TODO
{- prop :: RIO <{\x -> true}, {\w1 x w2 -> counter1 w2 < counter2 w2}> () @-}
prop :: RIO ()
prop = whileM condM incr'  
