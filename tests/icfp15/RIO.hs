module RIO where

{-@ data RIO a <pre :: World -> Prop, post :: World -> a -> World -> Prop> 
  = RIO (rs :: (x:World<pre> -> (a, World)<\w -> {v:World<post x w> | true}>))
  @-}
data RIO a  = RIO {runState :: World -> (a, World)}

{-@ runState :: forall <pre :: World -> Prop, post :: World -> a -> World -> Prop>. 
                RIO <pre, post> a -> x:World<pre> -> (a, World)<\w -> {v:World<post x w> | true}> @-}

data World  = W

instance Monad RIO where
{-@ instance Monad RIO where
 >>= :: forall < pre   :: World -> Prop 
               , pre2  :: a -> World -> Prop 
               , p     :: a -> Prop
               , post1 :: World -> a -> World -> Prop
               , post2 :: a -> World -> b -> World -> Prop
               , post :: World -> b -> World -> Prop>.
       {x::a<p>, w::World<pre>|- World<post1 w x> <: World<pre2 x>}
       {y::a, w::World<pre>, w2::World<pre2 y>, x::b, y::a<p> |- World<post2 y w2 x> <: World<post w x>}     
       {x::a, w::World, w2::World<post1 w x>|- {v:a | v = x} <: a<p>}   
       RIO <pre, post1> a
    -> (x:a<p> -> RIO <{v:World<pre2 x> | true}, \w1 y -> {v:World<post2 x w1 y> | true}> b)
    -> RIO <pre, post> b ;
 >>  :: forall < pre   :: World -> Prop 
               , pre2  :: World -> Prop 
               , post1 :: World -> a -> World -> Prop
               , post2 :: World -> b -> World -> Prop
               , post :: World -> b -> World -> Prop>.
       {x::a, w::World<pre>|- World<post1 w x> <: World<pre2>}
       {w::World<pre>, w2::World<pre2>, x::b, y::a |- World<post2 w2 x> <: World<post w x>}     
       RIO <pre, post1> a
    -> RIO <pre2, post2> b
    -> RIO <pre, post> b  ;
 return :: forall <p :: World -> Prop>.
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
