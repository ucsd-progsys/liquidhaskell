{-# LANGUAGE CPP #-}
module RIO2 where

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif

{-@ data RIO a <p :: World -> Bool, q :: World -> a -> World -> Bool>
  = RIO (rs :: (x:World<p> -> (a, World)<\w -> {v:World<q x w> | true}>))
  @-}
data RIO a  = RIO {runState :: World -> (a, World)}

{-@ runState :: forall <p :: World -> Bool, q :: World -> a -> World -> Bool>.
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
 >>= :: forall < p  :: World -> Bool
               , p2 :: a -> World -> Bool
               , r  :: a -> Bool
               , q1 :: World -> a -> World -> Bool
               , q2 :: a -> World -> b -> World -> Bool
               , q  :: World -> b -> World -> Bool>.
       {x::a<r>, w::World<p>|- World<q1 w x> <: World<p2 x>}
       {w::World<p>, x::a, w1::World<q1 w x>, y::b |- World<q2 x w1 y> <: World<q w y>}
       {x::a, w::World, w2::World<q1 w x>|- {v:a | v = x} <: a<r>}
       RIO <p, q1> a
    -> (x:a<r> -> RIO <{v:World<p2 x> | true}, \w1 y -> {v:World<q2 x w1 y> | true}> b)
    -> RIO <p, q> b ;
 >>  :: forall < p   :: World -> Bool
               , p2  :: World -> Bool
               , q1 :: World -> a -> World -> Bool
               , q2 :: World -> b -> World -> Bool
               , q :: World -> b -> World -> Bool>.
       {x::a, w::World<p>|- World<q1 w x> <: World<p2>}
       {w::World<p>, w2::World<p2>, x::b, y::a |- World<q2 w2 x> <: World<q w x>}
       RIO <p, q1> a
    -> RIO <p2, q2> b
    -> RIO <p, q> b  ;
 return :: forall <p :: World -> Bool>.
           x:a -> RIO <p, \w0 y -> {w1:World<p> | w0 == w1 && y == x}> a
  @-}
  (RIO g) >>= f = RIO $ \x -> case g x of {(y, s) -> (runState (f y)) s}
  (RIO g) >>  f = RIO $ \x -> case g x of {(y, s) -> (runState f    ) s}
  return w      = RIO $ \x -> (w, x)
  fail          = error

{-@ qualif Papp4(v:a, x:b, y:c, z:d, p:Pred a b c d) : papp4(p, v, x, y, z)     @-}

-- Test Cases:
-- * TestM (Basic)
-- * TwiceM
-- * IfM
-- * WhileM
