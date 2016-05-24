module WhileTest where

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-pattern-inline" @-}

import RIO
import WhileM

-------------------------------------------------------------------------------
----------------------------- whileM client -----------------------------------
-------------------------------------------------------------------------------
{-@ measure counter :: World -> Int @-}


whileTest       :: RIO ()
{-@ whileTest   :: RIO <{\x -> true}, {\w1 x w2 -> counter w2 <= 0}> () @-}
whileTest       = whileM (checkGtZero) (decrM)
  where
    checkGtZero = do {x <- get; return $ x > 0}


whileTest1       :: RIO ()
{-@ whileTest1   :: RIO <{\x -> counter x >= 0}, {\w1 x w2 -> counter w2 == 0}> () @-}
whileTest1       = whileM (checkGtZero) (decrM)
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
qual1 = undefined

{-@ qual2 :: RIO <{\x -> true}, {\w1 b w2 -> Prop b <=> counter w2 /= 0}> Bool @-}
qual2 :: RIO Bool
qual2 = undefined
