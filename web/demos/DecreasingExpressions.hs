module DecreasingExpressions where

range ::          Int -> Int -> [Int]
merge :: Ord a => [a] -> [a] -> [a]

-- | Termination on Increasing Arguments

{-@ range :: lo:Int -> hi:Int -> [Int] / [(hi - lo)] @-}

range lo hi | lo < hi   = lo : range (lo + 1) hi
            | otherwise = []


-- | Termination on a Function of the Arguments
{-@ type SL a = [a]<{\x v -> x <= v}> @-}

{-@ merge :: Ord a => xs:(SL a) -> ys:(SL a) -> (SL a) 
           / [(len xs) + (len ys)]                                    @-}

merge (x:xs) (y:ys) 
  | x < y     = x : merge xs     (y:ys)
  | otherwise = y : merge (x:xs) ys



