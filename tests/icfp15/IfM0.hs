module Ex1 where

{-@ LIQUID "--no-termination" @-}

import Language.Haskell.Liquid.Prelude 

{-@ data RIO a <pre :: World -> Prop, post :: World -> a -> World -> Prop, pp:: a -> Prop> 
  = RIO (rs :: (x:World<pre> -> (a<pp>, World)<\w -> {v:World<post x w> | true}>))
  @-}
data RIO a  = RIO {runState :: World -> (a, World)}

{-@ runState :: forall <pre :: World -> Prop, post :: World -> a -> World -> Prop, pp::a -> Prop>. 
                RIO <pre, post, pp> a -> x:World<pre> -> (a<pp>, World)<\w -> {v:World<post x w> | true}> @-}

data World  = W

{-@ bind :: forall < pre   :: World -> Prop 
               , pre2  :: World -> Prop 
               , p     :: a -> Prop
               , q     :: b -> Prop
               , post1 :: World -> a -> World -> Prop
               , post2 :: World -> b -> World -> Prop
               , post :: World -> b -> World -> Prop>.
       {w::World<pre>, x::a<p> |- World<post1 w x> <: World<pre2>}        
       {w::World<pre>, y::a<p>, w2::World<post1 w y>, x::b |- World<post2 w2 x> <: World<post w x>}        
       RIO <pre, post1, p> a
    -> (a<p> -> RIO <pre2, post2, q> b)
    -> RIO <pre, post, q> b @-}

bind :: RIO a -> (a -> RIO b) -> RIO b
bind (RIO g) f = RIO $ \x -> case g x of {(y, s) -> (runState (f y)) s} 


{-@
ifM  :: forall < pre   :: World -> Prop 
               , p :: World -> Bool -> World -> Prop
               , r1 :: World -> Prop
               , r2 :: World -> Prop
               , q :: Bool -> Prop
               , post1 :: World -> () -> World -> Prop
               , post  :: World -> () -> World -> Prop>.                  
       {b :: Bool<q>,   w :: World<pre>    |- World<p w b>      <: World<r1>        } 
       {b :: Bool<q>,   w :: World<pre>    |- World<p w b>      <: World<r2>        } 
       {w1::World<pre>, w2::World, y::()|- World<post1 w2 y> <: World<post w1 y>}
       RIO <pre, p, q> Bool 
       -> RIO <r1, post1, {\v -> true}> ()
       -> RIO <r2, post1, {\v -> true}> ()
       -> RIO <pre, post, {\v -> true}> ()
@-}
ifM :: RIO Bool -> RIO () -> RIO () -> RIO ()
ifM cond e1 e2
  = cond `bind` \g -> go g e1 e2

{-@
go  :: forall < pre   :: World -> Prop 
                 , r1 :: World -> Prop
                 , r2 :: World -> Prop
                 , pp :: () -> Prop
                 , post :: World -> () -> World -> Prop>.                               
      b:Bool
       -> RIO <{v:World<pre> | Prop b}, post, pp> ()
       -> RIO <{v:World<pre> | not (Prop b)}, post, pp> ()
       -> RIO <pre, post, pp> ()
@-}
go ::  Bool -> RIO () -> RIO () -> RIO ()
go cond e1 e2 = if cond then e1 else e2 









