module WhileM where

{-@ LIQUID "--no-pattern-inline" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}

import RIO

{-@
whileM  :: forall < p   :: World -> Prop
               , qc :: World -> Bool -> World -> Prop
               , qe :: World -> () -> World -> Prop
               , q  :: World -> () -> World -> Prop>.
       {x::(), s1::World<p>, b::{v:Bool | Prop v}, s2::World<qc s1 b> |- World<qe s2 x> <: World<p>}
       {b::{v:Bool | Prop v}, x2::(), s1::World<p>, s3::World |- World<q s3 x2> <: World<q s1 x2> }
       {b::{v:Bool | not (Prop v)}, x2::(), s1::World<p> |- World<qc s1 b> <: World<q s1 x2> }
          RIO <p, qc> Bool
       -> RIO <{\v -> true}, qe> ()
       -> RIO <p, q> ()
@-}
whileM :: RIO Bool -> RIO () -> RIO ()
whileM (RIO cond) (RIO e)
    = undefined
{-
    = RIO $ \s1 -> case cond s1 of {(y, s2) ->
       if y
        then case e s2 of {(y2, s3) -> runState (whileM (RIO cond) (RIO e)) s3}
        else ((), s2)
      }
-}

-- First Condition Used to be:
--        {x::(), s1::World<p>, b::{v:Bool | Prop v}, s2::World<qc s1 b> |- World<qe s2 x> <: World<p>}
--
-- But it got simplify to fit it one line

-------------------------------------------------------------------------------
----------------------------- whileM client -----------------------------------
-------------------------------------------------------------------------------
{-@ measure counter :: World -> Int @-}


whileTestUnSafe       :: RIO ()
{-@ whileTestUnSafe   :: RIO <{\x -> true}, {\w1 x w2 -> counter w2 == 0}> () @-}
whileTestUnSafe       = whileM checkGtZero decrM
  where
    checkGtZero = do {x <- get; return $ x > 0}


decrM :: RIO ()
{-@ decrM :: RIO <{\x -> true}, {\w1 x w2 -> counter w2 = (counter w1) - 1}> () @-}
decrM = undefined


get :: RIO Int
{-@ get :: forall <p :: World -> Prop >.
       RIO <p,\w x -> {v:World<p> | x = counter v && v == w}> Int @-}
get = undefined

{-@ qual99 :: n:Int -> RIO <{v:World | counter v >= 0}, \w1 b -> {v:World |  (Prop b <=> n >= 0) && (Prop b <=> counter v >= 0)}> {v:Bool | Prop v <=> n >= 0} @-}
qual99 :: Int -> RIO Bool
qual99 = undefined -- \x -> return (x >= 0)

{-@ qual3 :: m:Int ->  n:Int -> RIO <{v:World | counter v >= m}, \w1 b -> {v:World |  (Prop b <=> n >= m) && (Prop b <=> counter v >= m)}> {v:Bool | Prop v <=> n >= m} @-}
qual3 :: Int -> Int -> RIO Bool
qual3 = undefined -- \x -> return (x >= 0)

{-@ qual1 :: n:Int -> RIO <{v:World | counter v = n}, \w1 b -> {v:World |  (Prop b <=> n > 0) && (Prop b <=> counter v > 0)}> {v:Bool | Prop v <=> n > 0} @-}
qual1 :: Int -> RIO Bool
qual1 = \x -> return (x > 0)

{-@ qual2 :: RIO <{\x -> true}, {\w1 b w2 -> Prop b <=> counter w2 /= 0}> Bool @-}
qual2 :: RIO Bool
qual2 = undefined
