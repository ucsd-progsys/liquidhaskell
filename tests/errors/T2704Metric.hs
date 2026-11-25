{-@ LIQUID "--expect-error-containing=Desugaring can rename function parameters" @-}
-- | Like "T2704", for the termination metric of a local specification.
module T2704Metric where

step :: Int -> [Int] -> Int
step _ [] = 0
step n (m:_) = go m
  where
    {-@ go :: x:Int -> Int / [n - x] @-}
    go :: Int -> Int
    go x = if x < n then go (x + 1) else x
