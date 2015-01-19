module Ex1 where

import RIO

{-@ LIQUID "--no-termination" @-}


{-@ 
ifM  :: forall < pre   :: World -> Prop 
                 , post1 :: World -> () -> World -> Prop
                 , post :: World -> () -> World -> Prop>.
       {w:World<pre> -> y:() -> w2:World<pre> -> x:() -> World<post1 w2 x> -> World<post w x>}             
       RIO <pre, \w1 x -> {v:World<pre> | true}> Bool 
       -> RIO <pre, post1> () 
       -> RIO <pre, post1> ()  
       -> RIO <pre, post> ()
@-}
ifM :: RIO Bool -> RIO () -> RIO () -> RIO ()
ifM guard e1 e2 = do {g <- guard ; if g then e1 else e2}



