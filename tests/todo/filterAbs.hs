module Filter where

import Prelude hiding (filter)

{-@ filter :: forall <p :: a -> Prop, q :: a -> Bool -> Prop>.
                 {y:a<p> -> Bool<q y> -> {v:Bool | Prop v}}
               (x:a -> Bool<q x>) -> [a] -> [a<p>]
  @-}
filter _ [] = []
filter f (x:xs)
  | f x       = x : filter f xs
  | otherwise = filter f xs

{-@ isPos :: x:Int -> {v:Bool | Prop v <=> x > 0} @-}
isPos :: Int -> Bool
isPos n = n > 0

-- Now the below *should* work with
-- p := \v   -> 0 < v
-- q := \x v -> Prop v <=> 0 < 0


{-@ positives :: [Int] -> [{v:Int | v > 0}] @-}
positives xs = filter isPos xs
