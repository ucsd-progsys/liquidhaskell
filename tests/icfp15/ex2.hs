module Ex1 where

import RIO

{-@ LIQUID "--no-termination" @-}


{-@ 
ifM  :: forall < pre   :: World -> Prop 
                 , post1 :: World -> () -> World -> Prop
                 , post :: World -> () -> World -> Prop>.
       {w:World<pre> -> y:() -> w2:World<pre> -> x:() -> World<post1 w2 x> -> World<post w x>}             
       {w:World<pre> -> x:() -> {v:World | v = w} -> World<post1 w x>}

       {w:World -> w2:World -> x:a -> World<post1 w2 x> -> World<post w x>}        
       {w:World<pre> -> x:() -> {v:World | v = w} -> World<post w x>}
       {w:World<pre> -> x:() -> World<post1 w x> -> World<pre>}        
       {w:World<pre> -> y:() -> w2:World<post1 w y> -> x:() -> World<post w2 x> -> World<post w x>}        


       {w:World -> w2:World -> x:a -> World<post w2 x> -> World<post w x>}        
       {w:World<pre> -> x:() -> {v:World | v = w} -> World<post w x>}
       {w:World<pre> -> x:() -> World<post w x> -> World<pre>}        
       {w:World<pre> -> y:() -> w2:World<post w y> -> x:() -> World<post w2 x> -> World<post w x>}        



       RIO <pre, \w1 x -> {v:World<pre> | true}> Bool 
       -> RIO <pre, post1> () 
       -> RIO <pre, post> ()
@-}
ifM :: RIO Bool -> RIO () -> RIO ()
ifM guard e1 = do {g <- guard ; if g then do {e1; ifM guard e1} else return ()}



