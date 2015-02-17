module WhileM where

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}

import RIO 

{-@
whileM  :: forall < pre   :: World -> Prop 
               , p :: World -> Bool -> World -> Prop
               , pre1 :: World -> Prop
               , q :: Bool -> Prop
               , post1 :: World -> () -> World -> Prop
               , post  :: World -> () -> World -> Prop>. 
       {x::(), s1::World<pre>, b::{v:Bool<q> | Prop v}, s2::World<p s1 b> |- World<post1 s2 x> <: World<pre>}
       {b::{v:Bool<q> | Prop v}, x2::(), s1::World<pre>, s3::World |- World<post s3 x2> <: World<post s1 x2> } 
       {b::{v:Bool<q> | not (Prop v)}, x2::(), s1::World<pre> |- World<p s1 b> <: World<post s1 x2> } 
          RIO <pre, p, q> Bool 
       -> RIO <{\v -> true}, post1, {\v -> true}> ()
       -> RIO <pre, post, {\v -> true}> ()
@-}
whileM :: RIO Bool -> RIO () -> RIO ()
whileM (RIO cond) (RIO e) 
  = RIO $ \s1 -> case cond s1 of {(y, s2) -> 
       if y 
        then case e s2 of {(y2, s3) -> runState (whileM (RIO cond) (RIO e)) s3}
        else ((), s2)
      }

-------------------------------------------------------------------------------
----------------------------- whileM client ----------------------------------- 
-------------------------------------------------------------------------------
{-@ measure counter :: World -> Int @-}


whileTest       :: RIO ()
{-@ whileTest   :: RIO <{\x -> true}, {\w1 x w2 -> counter w2 <= 0 }, {\x -> true}> () @-}
whileTest       = whileM (checkGtZero) (decrM)
  where 
    checkGtZero = do {x <- get; return $ x > 0}


whileTest1       :: RIO ()
{-@ whileTest1   :: RIO <{\x -> counter x >= 0}, {\w1 x w2 -> counter w2 == 0}, {\x -> true}> () @-}
whileTest1       = whileM (checkGtZero) (decrM)
  where 
    checkGtZero = do {x <- get; return $ x > 0}


whileTestUnSafe       :: RIO ()
{-@ whileTestUnSafe   :: RIO <{\x -> true}, {\w1 x w2 -> counter w2 == 0}, {\x -> true}> () @-}
whileTestUnSafe       = whileM (checkGtZero) (decrM)
  where 
    checkGtZero = do {x <- get; return $ x > 0}


decrM :: RIO ()
{-@ decrM :: RIO <{\x -> true}, {\w1 x w2 -> counter w2 = (counter w1) - 1}, {\x -> true}> () @-}
decrM = undefined


get :: RIO Int 
{-@ get :: forall <p :: World -> Prop >. 
       RIO <p,\w x -> {v:World<p> | x = counter v && v == w}, {\v -> true}> Int @-} 
get = undefined 

{-@ qual99 :: n:Int -> RIO <{v:World | counter v >= 0}, \w1 b -> {v:World |  (Prop b <=> n >= 0) && (Prop b <=> counter v >= 0)}, {\v -> true}> {v:Bool | Prop v <=> n >= 0} @-}
qual99 :: Int -> RIO Bool
qual99 = undefined -- \x -> return (x >= 0)

{-@ qual1 :: n:Int -> RIO <{v:World | counter v = n}, \w1 b -> {v:World |  (Prop b <=> n > 0) && (Prop b <=> counter v > 0)}, {\v -> true}> {v:Bool | Prop v <=> n > 0} @-}
qual1 :: Int -> RIO Bool
qual1 = \x -> return (x > 0)

{-@ qual2 :: RIO <{\x -> true}, {\w1 b w2 -> Prop b <=> counter w2 /= 0}, {\v -> true}> Bool @-}
qual2 :: RIO Bool
qual2 = undefined