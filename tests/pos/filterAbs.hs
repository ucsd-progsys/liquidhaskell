{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}



module Filter where

import Prelude hiding (filter)

{-@ filter :: forall <p :: a -> Prop, q :: a -> Bool -> Prop>.
                  {y::a, flag::{v:Bool<q y> | Prop v} |- {v:a | v = y} <: a<p>}
                  (x:a -> Bool<q x>) -> [a] -> [a<p>]
  @-}

filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x       = x : filter f xs
  | otherwise = filter f xs
filter _ []   = []

{-@ isPos :: x:Int -> {v:Bool | Prop v <=> x > 0} @-}
isPos :: Int -> Bool
isPos n = n > 0


{-@ isNeg :: x:Int -> {v:Bool | Prop v <=> x < 0} @-}
isNeg :: Int -> Bool
isNeg n = n < 0


-- | `positives` works by instantiating:
-- p := \v   -> 0 < v
-- q := \x v -> Prop v <=> 0 < 0


{-@ positives :: [Int] -> [{v:Int | v > 0}] @-}
positives xs = filter isPos xs


-- | `negatives` works by instantiating:
-- p := \v   -> 0 > v
-- q := \x v -> Prop v <=> 0 > 0

{-@ negatives :: [Int] -> [{v:Int | v < 0}] @-}
negatives xs = filter isNeg xs
