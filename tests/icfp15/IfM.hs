module Ex1 where

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--diff" @-}
import Language.Haskell.Liquid.Prelude 

import RIO 

{-@ bind :: forall < pre   :: World -> Prop 
               , pre2  :: World -> Prop 
               , q     :: b -> Prop
               , p     :: a -> Prop
               , post1 :: World -> a -> World -> Prop
               , post2 :: World -> b -> World -> Prop
               , post :: World -> b -> World -> Prop>.
       {w::World<pre>, x::a<p> |- World<post1 w x> <: World<pre2>}  
       {w::World<pre>, x::a, w1::World<post1 w x> |- a <: a<p>}               
       {w::World<pre>, y::a<p>, w2::World<post1 w y>, x::b |- World<post2 w2 x> <: World<post w x>}        
       RIO <pre, post1> a
    -> (a<p> -> RIO <pre2, post2> b)
    -> RIO <pre, post> b @-}

bind :: RIO a -> (a -> RIO b) -> RIO b
bind (RIO g) f = RIO $ \x -> case g x of {(y, s) -> (runState (f y)) s} 


{-@  ret :: forall <p :: World -> Prop>.
           x:a -> RIO <p, \w0 y -> {w1:World<p> | w0 == w1 && y == x }> a
@-}

ret :: a -> RIO a 
ret = undefined



{-@
ifM  :: forall < pre   :: World -> Prop 
               , p :: World -> Bool -> World -> Prop
               , r1 :: World -> Prop
               , r2 :: World -> Prop
               , q :: Bool -> Prop
               , post1 :: World -> a -> World -> Prop
               , post  :: World -> a -> World -> Prop>.                  
       {b :: {v:Bool | Prop v},   w :: World<pre>    |- World<p w b>      <: World<r1>        } 
       {b :: {v:Bool | not (Prop v)},   w :: World<pre>    |- World<p w b>      <: World<r2>        } 
       {w1::World<pre>, w2::World, y::a|- World<post1 w2 y> <: World<post w1 y>}
       RIO <pre, p> Bool 
       -> RIO <r1, post1> a
       -> RIO <r2, post1> a
       -> RIO <pre, post> a
@-}
ifM :: RIO Bool -> RIO a -> RIO a -> RIO a
ifM (RIO cond) e1 e2
  = RIO $ \x -> case cond x of {(y, s) -> let f = \g -> if g then e1 else e2  in (runState (f y)) s} 


{-@ measure counter :: World -> Int @-}

get :: RIO Int 
{-@ get :: forall <p :: World -> Prop >. RIO <p,\w x -> {v:World<p> | 0 /= counter v && v == w}> Int @-} 
get = undefined 


{-@ checkZeroX :: RIO <{\x -> true}, {\w1 b w2 -> true}> Bool @-}
{- checkZeroX :: RIO <{\x -> true}, {\w1 b w2 -> Prop b <=> counter w2 /= 0}> Bool @-}
checkZeroX :: RIO Bool
checkZeroX = get `bind`  f 

{-@ f :: {v:Int | v /= 0} -> RIO Bool @-}
f :: Int -> RIO Bool
f = \x -> return (x /= 0)



divX       :: RIO Int 
{-@ divX   :: RIO <{\w -> (counter w) /= 0 }, {\w1 x w2 -> (counter w1) /= 0 && (counter w2) /= 0}> Int @-}
divX       = do {x <- get; return (100 `div` x)}

ifTest     :: RIO Int
ifTest     = ifM (checkZeroX) (divX) (return 10)



