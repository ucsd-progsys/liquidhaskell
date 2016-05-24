module IfM where

{-@ LIQUID "--no-pattern-inline" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}

import RIO

{-@
ifM  :: forall < p  :: World -> Prop
               , qc :: World -> Bool -> World -> Prop
               , p1 :: World -> Prop
               , p2 :: World -> Prop
               , qe :: World -> a -> World -> Prop
               , q  :: World -> a -> World -> Prop>.
       {b :: {v:Bool | Prop v},       w :: World<p> |- World<qc w b>  <: World<p1>    }
       {b :: {v:Bool | not (Prop v)}, w :: World<p> |- World<qc w b>  <: World<p2>    }
       {w1::World<p>, w2::World, y::a               |- World<qe w2 y> <: World<q w1 y>}
          RIO <p , qc> Bool
       -> RIO <p1, qe> a
       -> RIO <p2, qe> a
       -> RIO <p , q > a
@-}
ifM :: RIO Bool -> RIO a -> RIO a -> RIO a
ifM (RIO cond) e1 e2
  = RIO $ \x -> case cond x of {(y, s) -> runState (if y then e1 else e2) s}

{-@ measure counter :: World -> Int @-}



-------------------------------------------------------------------------------
------------------------------- ifM client ------------------------------------
-------------------------------------------------------------------------------

{-@
myif  :: forall < p :: World -> Prop
                , q :: World -> a -> World -> Prop>.
          b:Bool
       -> RIO <{v:World<p> |      Prop b }, q> a
       -> RIO <{v:World<p> | not (Prop b)}, q> a
       -> RIO <p , q > a
@-}
myif :: Bool -> RIO a -> RIO a -> RIO a
myif b e1 e2
  = if b then e1 else e2


-------------------------------------------------------------------------------
------------------------------- ifM client ------------------------------------
-------------------------------------------------------------------------------


ifTest0     :: RIO Int
{-@ ifTest0     :: RIO Int @-}
ifTest0     = ifM checkZeroX divX (return 10)
  where
    checkZeroX = do {x <- get; return $ x /= 0     }
    divX       = do {x <- get; return $ 100 `div` x}

ifTest1     :: RIO Int
{-@ ifTest1 :: RIO Int @-}
ifTest1     = ifM checkNZeroX (return 10) divX
  where
    checkNZeroX = do {x <- get; return $ x == 0     }
    divX        = do {x <- get; return $ 100 `div` x}

get :: RIO Int
{-@ get :: forall <p :: World -> Prop >.
       RIO <p,\w x -> {v:World<p> | x = counter v && v == w}> Int @-}
get = undefined



{-@ qual1 :: n:Int -> RIO <{v:World | counter v = n}, \w1 b -> {v:World |  (Prop b <=> n /= 0) && (Prop b <=> counter v /= 0)}> {v:Bool | Prop v <=> n /= 0} @-}
qual1 :: Int -> RIO Bool
qual1 = undefined

{-@ qual2 :: RIO <{\x -> true}, {\w1 b w2 -> Prop b <=> counter w2 /= 0}> Bool @-}
qual2 :: RIO Bool
qual2 = undefined

{-@ qual3 :: n:Int -> RIO <{v:World | counter v = n}, \w1 b -> {v:World |  (Prop b <=> n == 0) && (Prop b <=> counter v == 0)}> {v:Bool | Prop v <=> n == 0} @-}
qual3 :: Int -> RIO Bool
qual3 = undefined
{-@ qual4 :: RIO <{\x -> true}, {\w1 b w2 -> Prop b <=> counter w2 == 0}> Bool @-}
qual4 :: RIO Bool
qual4 = undefined
