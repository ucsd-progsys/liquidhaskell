module TwiceM where

{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-pattern-inline"   @-}

import RIO

{-@ measure counter :: World -> Int @-}

{-@ incr :: RIO <{\x -> counter x >= 0}, {\w1 s w2 -> counter w2 = counter w1 + 1 && s == counter w1}> Nat @-}
incr :: RIO Int
incr = undefined

{-@ get :: RIO <{\x -> counter x >= 0}, {\w1 s w2 -> w1 == w2 && s == w1}>  World  @-}
get :: RIO World
get = undefined




{-@ incr2 :: RIO <{\x -> counter x >= 0}, {\w1 x w2 -> counter w2 = counter w1 + 2  && x == counter w1 }> Nat @-}
incr2 :: RIO Int
incr2 = do x <- incr
           y <- incr
           return $ lassert (y > x) x

-- The following soundly fails
--            return $ lassert (y < x) x

-- The following impresicely fails
--            return $ lassert (y == x + 1) x


lassert :: Bool -> a -> a
{-@ lassert :: {v:Bool| Prop v} -> x:a -> {v:a | v == x} @-}
lassert b x = if b then x else error "lassert failure"
