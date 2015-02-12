module Ex1 where

import RIO

{-@ LIQUID "--no-termination" @-}

import Language.Haskell.Liquid.Prelude 

-- THIS TYPE CHECKS, BUT HOW CAN WE ACTUALLY USE IT?
{-@ 
ifM  :: forall < pre   :: World -> Prop 
                  , p :: World -> Bool -> World -> Prop
                  , r1 :: World -> Prop
                  , r2 :: World -> Prop
                  , post1 :: World -> () -> World -> Prop
                  , post2 :: World -> () -> World -> Prop
                  , post :: World -> () -> World -> Prop>.                  
       {x :: {v:Bool | true }, w :: World<pre> |- World<p w x> <: World<r1> }
       {x :: {v:Bool | true }, w :: World<pre> |- World<p w x> <: World<r2> }
       {w1::World, y::(), w2::World, x::() |- World<post1 w2 x> <: World<post w1 x>}             
       {w1::World, y::(), w2::World, x::() |- World<post2 w2 x> <: World<post w1 x>}             
       RIO <pre, p> Bool 
       -> RIO <r1, post1> ()
       -> RIO <r2, post2> ()
       -> RIO <pre, post> ()
@-}
ifM :: RIO Bool -> RIO () -> RIO () -> RIO ()
ifM cond e1 e2  = do{ g <- cond; if g then e1 else e2}