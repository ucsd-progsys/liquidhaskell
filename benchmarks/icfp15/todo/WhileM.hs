module WhileM where

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}

import RIO 

{-@
whileM  :: forall < p   :: World -> Prop 
               , qc :: World -> Bool -> World -> Prop
               , qe :: World -> () -> World -> Prop
               , q  :: World -> () -> World -> Prop>. 
       {x::(), s1::World<p>, b::{v:Bool | Prop v}, s2::World<qc s1 b> |- World<qe s2 x> <: World<p>}
       {b::{v:Bool | Prop v}, x2::(), s1::World<p>, s3::World |- World<q s3 x2> <: World<q s1 x2> } 
       {b::{v:Bool | not (Prop v)}, x2::(), s1::World<p> |- World<qc s1 b> <: World<q s1 x2> } 
          RIO <p, qc> Bool 
       -> RIO <{\v -> true}, qe> ()
       -> RIO <p, q> ()
@-}
whileM :: RIO Bool -> RIO () -> RIO ()
whileM (RIO cond) (RIO e) 
    = RIO $ \s1 -> case cond s1 of {(y, s2) -> 
       if y 
        then case e s2 of {(y2, s3) -> runState (whileM (RIO cond) (RIO e)) s3}
        else ((), s2)
      }