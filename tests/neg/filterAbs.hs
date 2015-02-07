{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}



module Filter where

import Prelude hiding (filter)

{-@ filter :: forall <p :: a -> Prop, q :: a -> Bool -> Prop>.
                  {y::a, flag :: {v:Bool<q y> | Prop v} |- {v:a | v = y} <: a<p>}
                  (x:a -> Bool<q x>) -> [a] -> [a<p>]
  @-}

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


-- Now the below *should* work with
-- p := \v   -> 0 < v
-- q := \x v -> Prop v <=> 0 < 0


{-@ positives :: [Int] -> [{v:Int | v > 0}] @-}
positives xs = filter isPos xs

{-@ negatives :: [Int] -> [{v:Int | v < 0}] @-}
negatives xs = filter isNeg xs

{-@ positivesBAD :: [Int] -> [{v:Int | v < 0}] @-}
positivesBAD xs = filter isPos xs

