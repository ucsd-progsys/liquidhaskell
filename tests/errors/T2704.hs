{-@ LIQUID "--expect-error-containing=Desugaring can rename function parameters" @-}
-- | Desugaring renames the parameter @n@ of @step@, because it is not bound in
-- the first equation. The error should tell that this can happen, and where to
-- find workarounds.
module T2704 where

{-@ type Bounded B = { m : Int | m < B } @-}

{-@ step :: b : Int -> [Bounded b] -> [Bounded (b + 1)] @-}
step :: Int -> [Int] -> [Int]
step _ [] = []
step n ms = go ms
  where
    {-@ go :: [Bounded n] -> [Bounded (n + 1)] @-}
    go :: [Int] -> [Int]
    go [] = []
    go (x:xs) = (x + 1) : go xs
