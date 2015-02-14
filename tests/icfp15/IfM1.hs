module Ex1 (ifTest) where

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
               , pre1  :: World -> Prop 
               , pre2  :: World -> Prop 
               , p     :: a -> Prop
               , pp    :: a -> Prop
               , q     :: b -> Prop
               , post1 :: World -> a -> World -> Prop
               , post2 :: World -> b -> World -> Prop
               , post :: World -> b -> World -> Prop>.
       {World<pre1> <: World<pre>}
       {w::World<pre>, x::a<p> |- World<post1 w x> <: World<pre2>}        
       {w::World<pre>, w2::World<pre2>, x::b |- World<post2 w2 x> <: World<post w x>}     
       {x::a, w::World, w2::World<post1 w x>|- {v:a | v = x} <: a<p>}   
       RIO <pre, post1, pp> a
    -> (a<p> -> RIO <pre2, post2, q> b)
    -> RIO <pre1, post, q> b @-}

bind :: RIO a -> (a -> RIO b) -> RIO b
bind (RIO g) f = RIO $ \x -> case g x of {(y, s) -> (runState (f y)) s} 


{-@
ifM  :: forall < pre   :: World -> Prop 
               , p :: World -> Bool -> World -> Prop
               , r1 :: World -> Prop
               , r2 :: World -> Prop
               , q :: Bool -> Prop
               , post1 :: World -> a -> World -> Prop
               , post  :: World -> a -> World -> Prop>.                  
       {b :: {v:Bool<q> | Prop v},   w :: World<pre>    |- World<p w b>      <: World<r1>        } 
       {b :: {v:Bool<q> | not (Prop v)},   w :: World<pre>    |- World<p w b>      <: World<r2>        } 
       {w1::World<pre>, w2::World, y::a|- World<post1 w2 y> <: World<post w1 y>}
          RIO <pre, p, q> Bool 
       -> RIO <r1, post1, {\v -> true}> a
       -> RIO <r2, post1, {\v -> true}> a
       -> RIO <pre, post, {\v -> true}> a
@-}
ifM :: RIO Bool -> RIO a -> RIO a -> RIO a
ifM (RIO cond) e1 e2 
  = 
    RIO $ \x -> case cond x of {(y, s) -> let f g = go g e1 e2 in (runState (f y)) s} 




{-@
go  :: forall < pre   :: World -> Prop 
                 , r1 :: World -> Prop
                 , r2 :: World -> Prop
                 , pp :: a -> Prop
                 , post :: World -> a -> World -> Prop>.                               
      b:Bool
       -> RIO <{v:World<pre> | Prop b}, post, pp> a
       -> RIO <{v:World<pre> | not (Prop b)}, post, pp> a
       -> RIO <pre, post, pp> a
@-}
go ::  Bool -> RIO a -> RIO a -> RIO a
go cond e1 e2 = if cond then e1 else e2 


{-@ measure counter :: World -> Int @-}

get :: RIO Int 
{-@ get :: forall <p :: World -> Prop >. 
       RIO <p,\w x -> {v:World<p> | x = counter v && v == w && x = counter w}, {\v -> true}> Int @-} 
get = undefined 


{-@ checkZeroX :: RIO <{\x -> true}, {\w1 b w2 -> Prop b => counter w2 /= 0}, {\v -> true}> Bool @-}
checkZeroX :: RIO Bool
checkZeroX = get `bind` f 

{-@ f :: n:Int -> RIO <{v:World | counter v = n}, \w1 b -> {v:World |  (Prop b => n /= 0) && (Prop b => counter v /= 0)}, {\v -> true}> {v:Bool | Prop v <=> n /= 0} @-}
f :: Int -> RIO Bool
f = \x -> ret (x /= 0)

{-@  ret :: forall <p :: World -> Prop>.
           x:a -> RIO <p, \w0 y -> {w1:World<p> | w0 == w1 && y == x }, {\v -> v = x}> a
@-}

ret :: a -> RIO a 
ret = undefined


divX       :: RIO Int 
{- divX   :: RIO <{\w -> (counter w) /= 0 }, {\w1 x w2 -> (counter w1) /= 0 && (counter w2) /= 0}, {\v -> true}> Int @-}
divX       = get `bind` bar 



bar :: Int -> RIO Int
{-@ bar :: {v:Int | v /= 0} -> RIO Int @-}
bar = \x -> ret (100 `div` x)

ifTest     :: RIO Int
ifTest     = ifM (checkZeroX) (divX) (ret 10)









{-@ qualif FOO3(v:World, b:bool, r:Pred World, w:World, p:Pred World World Bool): (((papp3 p v w b) && Prop b) => (papp1 r v)) @-}
{-@ qualif FOO1(v:World, b:bool, r:Pred World, w:World, p:Pred World World Bool): (((papp3 p v w b) && Prop b) => (papp1 r v)) @-}
{-@ qualif FOO2(v:World, b:bool, r:Pred World): ((not (Prop b)) => (papp1 r v)) @-}
{-@ qualif FOO4(v:World, b:bool, r:Pred World): ((Prop b) && (papp1 r v)) @-}
{-@ qualif FOO5(v:World, r:Pred World): ((papp1 r v)) @-}






