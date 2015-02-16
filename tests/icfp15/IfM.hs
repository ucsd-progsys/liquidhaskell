module IfM where

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}

import RIO 

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
  = RIO $ \x -> case cond x of {(y, s) -> runState (if y then e1 else e2) s} 

{-@ measure counter :: World -> Int @-}


-------------------------------------------------------------------------------
------------------------------- ifM client ------------------------------------ 
-------------------------------------------------------------------------------


ifTest0     :: RIO Int
{-@ ifTest0     :: RIO Int @-}
ifTest0     = ifM (checkZeroX) (divX) (return 10)
  where 
    checkZeroX = do {x <- get; return $ x /= 0     }
    divX       = do {x <- get; return $ 100 `div` x}

ifTest1     :: RIO Int
{-@ ifTest1     :: RIO Int @-}
ifTest1     = ifM (checkNZeroX) (return 10) divX
  where 
    checkNZeroX = do {x <- get; return $ x == 0     }
    divX        = do {x <- get; return $ 100 `div` x}



ifTestUnsafe0     :: RIO Int
{-@ ifTestUnsafe0     :: RIO Int @-}
ifTestUnsafe0     = ifM (checkZeroX) (return 10) divX
  where 
    checkZeroX = do {x <- get; return $ x /= 0     }
    divX       = do {x <- get; return $ 100 `div` x}

ifTestUnsafe1     :: RIO Int
{-@ ifTestUnsafe1     :: RIO Int @-}
ifTestUnsafe1     = ifM (checkNZeroX) divX (return 10)
  where 
    checkNZeroX = do {x <- get; return $ x == 0     }
    divX        = do {x <- get; return $ 100 `div` x}


get :: RIO Int 
{-@ get :: forall <p :: World -> Prop >. 
       RIO <p,\w x -> {v:World<p> | x = counter v && v == w}, {\v -> true}> Int @-} 
get = undefined 



{-@ qual1 :: n:Int -> RIO <{v:World | counter v = n}, \w1 b -> {v:World |  (Prop b <=> n /= 0) && (Prop b <=> counter v /= 0)}, {\v -> true}> {v:Bool | Prop v <=> n /= 0} @-}
qual1 :: Int -> RIO Bool
qual1 = \x -> return (x /= 0)

{-@ qual2 :: RIO <{\x -> true}, {\w1 b w2 -> Prop b <=> counter w2 /= 0}, {\v -> true}> Bool @-}
qual2 :: RIO Bool
qual2 = undefined

{-@ qual3 :: n:Int -> RIO <{v:World | counter v = n}, \w1 b -> {v:World |  (Prop b <=> n == 0) && (Prop b <=> counter v == 0)}, {\v -> true}> {v:Bool | Prop v <=> n == 0} @-}
qual3 :: Int -> RIO Bool
qual3 = \x -> return (x == 0)

{-@ qual4 :: RIO <{\x -> true}, {\w1 b w2 -> Prop b <=> counter w2 == 0}, {\v -> true}> Bool @-}
qual4 :: RIO Bool
qual4 = undefined