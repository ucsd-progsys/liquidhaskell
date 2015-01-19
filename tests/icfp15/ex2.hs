module Ex1 where

import RIO

{-@ LIQUID "--no-termination" @-}


{-@ 
whileM  :: forall < pre   :: World -> Prop 
                  , post1 :: World -> () -> World -> Prop
                  , post :: World -> () -> World -> Prop>.
       {w:World<pre> -> y:() -> w2:World<pre> -> x:() -> World<post1 w2 x> -> World<post w x>}             
       {w:World<pre> -> x:() -> {v:World | v = w} -> World<post1 w x>}
       {w:World<pre> -> x:() -> {v:World | v = w} -> World<post w x>}
       {w:World<pre> -> x:() -> World<post w x> -> World<pre>}        
       RIO <pre, \w1 x -> {v:World<pre> | true}> Bool 
       -> RIO <pre, post1> () 
       -> RIO <pre, post> ()
@-}
whileM :: RIO Bool -> RIO () -> RIO ()
whileM guard e1 = do {g <- guard ; if g then do {e1; whileM guard e1} else return ()}



