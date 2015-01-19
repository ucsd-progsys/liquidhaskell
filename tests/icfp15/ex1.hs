module Ex1 where

import RIO

{-@ LIQUID "--no-termination" @-}


{-@ 
ifM  :: forall < pre   :: World -> Prop 
                 , post1 :: World -> a -> World -> Prop
                 , post :: World -> a -> World -> Prop>.
       {w:World<pre> -> y:a -> w2:World<pre> -> x:a -> World<post1 w2 x> -> World<post w x>}        
       RIO <pre, \w1 x -> {v:World<pre> | true}> Bool 
       -> RIO <pre, post1> a  
       -> RIO <pre, post1> a  
       -> RIO <pre, post> a 
@-}
ifM :: RIO Bool -> RIO a -> RIO a -> RIO a
ifM guard e1 e2 = do {g <- guard ; if g then e1 else e2}



