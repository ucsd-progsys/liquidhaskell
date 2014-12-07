module LocalTermExpr where

{-@ assume (!!) :: xs:[a] -> {v:Nat | v < len xs} -> a @-}

mysum xs = go 0 0
  where
    i = 0
    n = length xs
    {-@ go :: i:_ -> _ -> _ / [len xs - i] @-}
    go i acc
      | i >= n    = acc
      | otherwise = go (i+1) (acc + xs !! i)

myfoo = foo 5 True
  where
    n = False
    {-@ foo :: n:_ -> b:{_ | n >= 0 && Prop b} -> {v:_ | n >= 0 && (Prop b)} / [n-0] @-}
    foo :: Int -> Bool -> Bool
    foo 0 _ = True
    foo n b = foo (n-1) b
