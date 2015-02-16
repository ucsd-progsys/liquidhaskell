module WhileM where

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}

import RIO 
import IfM

{-@
whileM  :: forall < pre   :: World -> Prop 
               , p :: World -> Bool -> World -> Prop
               , r1 :: World -> Prop
               , r2 :: World -> Prop
               , q :: Bool -> Prop
               , post1 :: World -> () -> World -> Prop
               , post  :: World -> () -> World -> Prop>. 
       {x::(), s1::World<pre>, b::Bool<q>, s2::World<p s1 b> |- World<post1 s2 x> <: World<pre>}
       {x1::(), x2::(), s1::World, s3::World |- World<post s3 x2> <: World<post s1 x2> } 
       {s1::World, b::{v:Bool<q> |  not (Prop v)}, x :: () |- World<p s1 b> <: World<post s1 x> } 
          RIO <pre, p, q> Bool 
       -> RIO <{\x -> true}, post1, {\v -> true}> ()
       -> RIO <pre, post, {\v -> true}> ()
@-}
whileM :: RIO Bool -> RIO () -> RIO ()
whileM (RIO cond) (RIO e) 
  = RIO $ \s1 -> case cond s1 of {(y, s2) -> 
       if y 
        then case e s2 of {(y2, s3) -> runState (whileM (RIO cond) (RIO e)) s3}
        else ((), s2)
      }