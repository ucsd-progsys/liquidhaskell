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


{-
ifM'  :: forall < pre   :: World -> Prop 
                  , p :: World -> Bool -> World -> Prop
                  , r1 :: World -> Prop
                  , r2 :: World -> Prop
                  , post :: World -> () -> World -> Prop>.                  
       {b :: {v:Bool | Prop v}, w :: World |- {v:World<p w b> | true} <: World<r1> }
       RIO <pre, p> Bool 
       -> RIO <r1, {\x y z -> true}> ()
       -> RIO <pre, {\x y z -> true}> ()
@-}
-- ifM' :: RIO Bool -> RIO () -> RIO ()
-- ifM' cond e1  = cond `bind` \g -> ifM'' g e1 
-- ifM' (RIO cond) e1 = let f = \g -> ifM'' g e1 in 
--                      RIO $ \x -> case cond x of {(y, s) -> (runState ((let f = \g -> ifM'' g e1 in f) y)) s} 

{-@
ifM0, ifM'''  :: forall < pre   :: World -> Prop 
                  , p :: World -> Bool -> World -> Prop
                  , r1 :: World -> Prop
                  , r2 :: World -> Prop
                  , q1 :: Bool -> Prop
                  , post :: World -> () -> World -> Prop>.                  
       {b1 :: {v:Bool<q1> | true}, b::{v:Bool | v = b1}, w :: World |- {v:World<p w b> | true} <: World<r1> }
       RIO <pre, p, q1> Bool 
       -> RIO <r1, {\x y z -> true}, {\v -> true}> ()
       -> RIO <pre, {\x y z -> true}, {\v -> true}> ()
@-}
ifM0, ifM''' :: RIO Bool -> RIO () -> RIO ()
ifM''' cond e1
  = cond `bind` ifM'' e1
ifM0 (RIO cond) e1 
  = RIO $ \x -> case cond x of {(y, s) -> (runState ((let f g = ifM'' e1 g in f) y)) s} 



{-
p => post1 

-}

-- ifM' (RIO cond) e1 e2 = RIO $ \x -> case cond x of {(y, s) -> (runState ((\g -> ifM'' g e1 e2) y)) s} 


{-@ 
ifM''  :: forall < pre   :: World -> Prop 
                 , r1 :: World -> Prop
                 , r2 :: World -> Prop
                 , pp :: Bool -> Prop
                 , post :: World -> () -> World -> Prop>.                               
          RIO <{v:World<pre> | true}, post, {\v -> true}> ()
       -> Bool<pp>
       -> RIO <pre, post, {\v -> true}> ()
@-}
ifM'' ::  RIO () -> Bool -> RIO ()
ifM'' cond e1 = undefined -- if cond then e1 else e2 









{-@ qualif FOO3(v:World, b:bool, r:Pred World, w:World, p:Pred World World Bool): (((papp3 p v w b) && Prop b) => (papp1 r v)) @-}
{-@ qualif FOO1(v:World, b:bool, r:Pred World, w:World, p:Pred World World Bool): (((papp3 p v w b) && Prop b) => (papp1 r v)) @-}
{-@ qualif FOO2(v:World, b:bool, r:Pred World): ((not (Prop b)) => (papp1 r v)) @-}
{-@ qualif FOO4(v:World, b:bool, r:Pred World): ((Prop b) && (papp1 r v)) @-}
{-@ qualif FOO5(v:World, r:Pred World): ((papp1 r v)) @-}

















