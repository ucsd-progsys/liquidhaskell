module LocalTermExpr where

{-@ assume (!!) :: xs:[a] -> {v:Nat | v < len xs} -> a @-}

mysum xs = go 0 0
  where
    n = length xs
    {-@ go :: i:_ -> _ -> _ / [nn - i] @-}
    go i acc
      | i >= n    = acc
      | otherwise = go (i+1) (acc + xs !! i)
