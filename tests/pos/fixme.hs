module Fixme () where

{-@ LIQUID "--no-termination" @-}
{-@ type SL a = [a]<{\x v -> x <= v}> @-}

{-@ merge :: Ord a => (SL a) -> (SL a) -> (SL a) @-}
merge :: Ord a => [a] -> [a] -> [a]
merge xss@(x:xs) (y:ys)
  | x < y     = x : merge xs (y:ys)
-- this is safe
--   | otherwise = y : merge (x:xs) ys
-- but this isn't
  | otherwise = y : merge xss ys

