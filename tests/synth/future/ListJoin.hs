{-@ LIQUID "--typed-holes" @-}

module ListJoin where

import Language.Haskell.Liquid.Synthesize.Error

-- Variable introduction for map's function
{-@ map' :: (a -> b) -> x: [a] -> { v: [b] | len v == len x } @-}
map' :: (a -> b) -> [a] -> [b]
map' = map

{-@ append' :: x: [a] -> y: [a] -> { v: [a] | len v == len x + len y } @-}
append' :: [a] -> [a] -> [a]
append' xs ys = xs ++ ys

{-@ join' :: x: [a] -> y: [b] -> { v: [(a, b)] | len v == len x * len y } @-}
join' :: [a] -> [b] -> [(a, b)]
join' = _goal
