module WhileM where

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}

import RIO 
import IfM

{-@
whileM  :: forall < pre   :: World -> Prop 
               , p :: World -> Bool -> World -> Prop
               , r1 :: World -> Prop
               , r2 :: World -> Prop
               , q :: Bool -> Prop
               , post1 :: World -> () -> World -> Prop
               , post  :: World -> () -> World -> Prop>. 
       {b :: {v:Bool<q> | true}, w :: World<pre>, x::() |- World<p w b> <: World<post w x> } 
       {x1::(), x2::(), w1::World, w2::World |- World<post w1 x2> <: World<post w2 x2> } 
       {x2::(), w2::World<pre> |- World<pre> <: World<post w2 x2> } 
          RIO <pre, p, q> Bool 
       -> RIO <{\x -> true}, post1, {\v -> true}> ()
       -> RIO <{\x -> true}, post, {\v -> true}> ()
@-}
whileM :: RIO Bool -> RIO () -> RIO ()
whileM (RIO cond) (RIO e) 
  = RIO $ \x -> case cond x of {(y, s) -> 
       if y 
        then runSt1 (
          RIO $ \x2 -> case e x2 of {(y2, s2) -> runSt2 (whileM (RIO cond) (RIO e)) s2}
          ) s 
        else ((), s)
      }
  where 
    runSt1 (RIO f) s = f s
    runSt2 (RIO f) s = f s



--   (RIO g) >>  f = RIO $ \x -> case g x of {(y, s) -> (runState f    ) s}    



{-
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
-- ifM :: RIO Bool -> RIO a -> RIO a -> RIO a
-- ifM (RIO cond) e1 e2 
--   = RIO $ \x -> case cond x of {(y, s) -> runState (if y then e1 else e2) s} 



{-@
go  :: forall < pre   :: World -> Prop 
               , p :: World -> () -> World -> Prop
               , r1 :: World -> Prop
               , r2 :: World -> Prop
               , q :: Bool -> Prop
               , pre1 :: World -> Prop
               , post1 :: World -> () -> World -> Prop
               , post  :: World -> () -> World -> Prop>. 
          {b::(), w::World|- World<p w b> <: World<pre1>}
          {y::(), x::(), w1::World, w2 :: World|- World<post1 w2 x> <: World<post w1 y>}
          {w1::World<pre>, y::() |- {v:World<pre> | v = w1} <: World<post w1 y>}
          b:Bool 
       -> RIO <{v:World<pre> | Prop b}, p, {\v -> true}> () 
       -> RIO <pre1, post1, {\v -> true}> ()
       -> RIO <pre, post, {\v -> true}> ()
@-}
go :: Bool -> RIO () -> RIO () -> RIO ()
-- go x (RIO g) f
--   = RIO $ \x -> case g x of {(y, s) -> (runState f) s} 
-- go x e act = RIO $ \x -> ((), x)
go = undefined
--   = if x then do {e; act} else return ()
--   = if x 
--      then RIO $ \x -> case e x of {(y, s) -> (runState act    ) s}  
--      else return ()
--   = if x then do {e; act} else return ()


{-
          {y::(),  w1::World     |- {v:World<pre> | v = w1} <: World<post w1 y>}
          {y::(), x::(), w1::World, w2 :: World|- World<post1 w2 x> <: World<post w1 y>}


-}

-------------------------------------------------------------------------------
----------------------------- whileM client ----------------------------------- 
-------------------------------------------------------------------------------
{- measure counter :: World -> Int @-}



{-@ qual1 :: n:Int -> RIO <{v:World | counter v = n}, \w1 b -> {v:World |  (Prop b <=> n > 0) && (Prop b <=> counter v > 0)}, {\v -> true}> {v:Bool | Prop v <=> n > 0} @-}
qual1 :: Int -> RIO Bool
qual1 = \x -> return (x > 0)

{-@ qual2 :: RIO <{\x -> true}, {\w1 b w2 -> Prop b <=> counter w2 /= 0}, {\v -> true}> Bool @-}
qual2 :: RIO Bool
qual2 = undefined