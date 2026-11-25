{-@ LIQUID "--expect-error-containing=Desugaring can rename function parameters" @-}
-- | Like "T2704", for a local assumed specification.
module T2704Assume where

step :: Int -> [Int] -> Int
step _ [] = 0
step n (m:_) = go m
  where
    {-@ assume go :: Int -> {v:Int | v < n} @-}
    go :: Int -> Int
    go x = x
