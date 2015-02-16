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
       {b :: {v:Bool<q> | true}, w :: World<pre>, x::() |- World<p w b> <: World<post w x> } 
       {x1::(), x2::(), w1::World, w2::World |- World<post w1 x2> <: World<post w2 x2> } 
       {s1::World, b::{v:Bool<q> |      (Prop v)}, x :: () |- World<p s1 b> <: World<post s1 x> } 
       {s1::World, b::{v:Bool<q> |  not (Prop v)}, x :: () |- World<p s1 b> <: World<post s1 x> } 
          RIO <{\x -> true}, p, q> Bool 
       -> RIO <{\x -> true}, post1, {\v -> true}> ()
       -> RIO <{\x -> true}, post, {\v -> true}> ()
@-}
whileM :: RIO Bool -> RIO () -> RIO ()
whileM (RIO cond) (RIO e) 
  = RIO $ \s1 -> case cond s1 of {(y, s2) -> 
       if y 
        then case e s2 of {(y2, s3) -> runState (whileM (RIO cond) (RIO e)) s3}
        else ((), s2)
      }
