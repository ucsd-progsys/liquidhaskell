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
               , pre2  :: World -> Prop 
               , p     :: a -> Prop
               , post1 :: World -> a -> World -> Prop
               , post2 :: World -> b -> World -> Prop
               , post :: World -> b -> World -> Prop>.
       {w::World<pre>, x::a |- World<post1 w x> <: World<pre2>}        
       {w::World<pre>, x::a, w1::World<post1 w x> |- a <: a<p>}        
       {w::World<pre>, y::a<p>, w2::World<post1 w y>, x::b |- World<post2 w2 x> <: World<post w x>}        
       RIO <pre, post1> a
    -> (a<p> -> RIO <pre2, post2> b)
    -> RIO <pre, post> b ;
 >>  :: forall < pre   :: World -> Prop 
               , pre2  :: World -> Prop 
               , post1 :: World -> a -> World -> Prop
               , post2 :: World -> b -> World -> Prop
               , post :: World -> b -> World -> Prop>.
       {w::World<pre>, x::a |- World<post1 w x> <: World<pre2>}        
       {w::World<pre>, y::a, w2::World<post1 w y>, x::b |- World<post2 w2 x> <: World<post w x>}        
       RIO <pre, post1> a
    -> RIO <pre2, post2> b
    -> RIO <pre, post> b ;
 return :: forall <p :: World -> Prop>.
           x:a -> RIO <p, \w0 y -> {w1:World<p> | w0 == w1 && y == x }> a
  @-}  
  (RIO g) >>= f = RIO $ \x -> case g x of {(y, s) -> (runState (f y)) s} 
  (RIO g) >>  f = RIO $ \x -> case g x of {(y, s) -> (runState f    ) s}    
  return w      = RIO $ \x -> (w, x)
  fail          = error
