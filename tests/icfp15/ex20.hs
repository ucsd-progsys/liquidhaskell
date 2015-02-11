module Ex1 where

import RIO

{-@ LIQUID "--no-termination" @-}



-- THIS TYPE CHECKS, BUT HOW CAN WE ACTUALLY USE IT?
{-@ 
whileM  :: forall < pre   :: World -> Prop 
                  , q :: World -> () -> World -> Prop
                  , p :: World -> Bool -> World -> Prop
                  , r :: World -> Prop
                  , post :: World -> () -> World -> Prop>.
       {x :: {v:Bool | not (Prop v)}, w :: World<pre>, y :: () |- World<p w x> <: World<post w y> }                   
       RIO <pre, p> Bool 
       -> RIO <r, q> () 
       -> RIO <pre, post> ()
@-}
whileM :: RIO Bool -> RIO () -> RIO ()
whileM cond e = undefined -- do {g <- guard ; if g then do {e1; whileM guard e1} else return ()}


{-@ measure counter1 :: World -> Int @-}
{-@ measure counter2 :: World -> Int @-}

{-@ incr' :: RIO <{\x -> true}, {\w1 x w2 -> counter1 w2 = counter1 w1 + 1}> () @-}
incr' :: RIO ()
incr' = undefined

{-@ condM :: RIO <{\x -> true}, {\w1 x w2 -> (Prop x) <=> counter1 w2 >= counter2 w2}> Bool @-}
condM :: RIO Bool
condM = undefined

{-@ propSAT :: RIO <{\x -> true}, {\w1 x w2 -> counter1 w2 < counter2 w2}> () @-}
propSAT :: RIO ()
propSAT = whileM condM incr'  

{-@ propUNSAT :: RIO <{\x -> true}, {\w1 x w2 -> counter1 w2 >= counter2 w2}> () @-}
propUNSAT :: RIO ()
propUNSAT = whileM condM incr'  
