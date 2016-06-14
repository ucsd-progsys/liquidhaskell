module RIO where

import Control.Applicative

{-@ data RIO a <p :: World -> Prop, q :: World -> a -> World -> Prop> 
  = RIO (rs :: (x:World<p> -> (a, World)<\w -> {v:World<q x w> | true}>))
  @-}
data RIO a  = RIO {runState :: World -> (a, World)}

{-@ runState :: forall <p :: World -> Prop, q :: World -> a -> World -> Prop>. 
                RIO <p, q> a -> x:World<p> -> (a, World)<\w -> {v:World<q x w> | true}> @-}

data World  = W


-- | RJ: Putting these in to get GHC 7.10 to not fuss
instance Functor RIO where
  fmap = undefined

-- | RJ: Putting these in to get GHC 7.10 to not fuss
instance Applicative RIO where
  pure  = undefined
  (<*>) = undefined 

instance Monad RIO where
{-@ instance Monad RIO where
  >>= :: forall < p  :: World -> Prop 
               , p2 :: a -> World -> Prop 
               , r  :: a -> Prop
               , q1 :: World -> a -> World -> Prop
               , q2 :: a -> World -> b -> World -> Prop
               , q  :: World -> b -> World -> Prop>.
       {x::a<r>, w::World<p>|- World<q1 w x> <: World<p2 x>}
       {w::World<p>, x::a<r>, w1:: World<q1 w x>, w2::{v:World<p2 x> | v == w1}, y::b|- World<q2 x w2 y> <: World<q w y>}     
       {x::a, w::World<p>, w2::World<q1 w x>|- {v:a | v = x} <: a<r>}   
       RIO <p, q1> a
    -> (x:a<r> -> RIO <{v:World<p2 x> | true}, \w1 y -> {v:World<q2 x w1 y> | true}> b)
    -> RIO <p, q> b ;
 >>  :: forall < p   :: World -> Prop 
               , p2  :: World -> Prop 
               , q1 :: World -> a -> World -> Prop
               , q2 :: World -> b -> World -> Prop
               , q :: World -> b -> World -> Prop>.
       {x::a, w::World<p>|- World<q1 w x> <: World<p2>}
       {w::World<p>, w2::World<p2>, y::a, w3:: {v:World<q1 w y> | v == w2}, x::b |- World<q2 w2 x> <: World<q w x>}     
       RIO <p, q1> a
    -> RIO <p2, q2> b
    -> RIO <p, q> b  ;
 return :: forall <p :: World -> Prop>.
           x:a -> RIO <p, \w0 y -> {w1:World | w0 == w1 && y == x}> a
  @-}  
  (RIO g) >>= f = RIO $ \x -> case g x of {(y, s) -> (runState (f y)) s} 
  (RIO g) >>  f = RIO $ \x -> case g x of {(y, s) -> (runState f    ) s}    
  return w      = RIO $ \x -> (w, x)
  fail          = error

{- qualif Papp4(v:a, x:b, y:c, z:d, p:Pred a b c d) : papp4(p, v, x, y, z)     @-}

-- Test Cases:
-- * TestM (Basic)
-- * TwiceM
-- * IfM
-- * WhileM  
