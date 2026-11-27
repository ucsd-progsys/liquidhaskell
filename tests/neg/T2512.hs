{-@ LIQUID "--expect-error-containing=is not a subtype of the required type" @-}
{-# LANGUAGE RankNTypes #-}
-- | Tests that the refinements of a signature are still checked when it has a
-- hole for an argument with a higher-rank type.
module T2512 where

{-@ app :: f:_ -> x:Int -> {v:Int | v = x} @-}
app :: (forall c. c -> c) -> Int -> Int
app f x = f x + 1
