module LocalTermExpr where

{-@ assume (!!) :: xs:[a] -> {v:Nat | v < len xs} -> a @-}

mysum xs = go 0 0
  where
    i = 0
    n = length xs
    {-@ go :: i:_ -> _ -> _ / [n - i] @-}
    go i acc
      | i >= n    = acc
      | otherwise = go (i+1) (acc + xs !! i)

myfoo = foo 5 True
  where
    n = False
    {-@ foo :: n:_ -> b:{_ | n >= 0 && b} -> {v:_ | n >= 0 && b} / [n] @-}
    foo :: Int -> Bool -> Bool
    foo 0 _ = True
    foo n b = foo (n-1) b

mysumFlipped xs = go 0 0
  where
    i = 0
    n = length xs
    {-@ go :: _ -> i:_ -> _ / [n - i] @-}
    go acc i
      | i >= n    = acc
      | otherwise = go (acc + xs !! i) (i+1)

myfooFlipped = foo True 5
  where
    n = False
    {-@ foo :: b:_ -> n:{_ | n >= 0 && b} -> {v:_ | n >= 0 && b} / [n] @-}
    foo :: Bool -> Int -> Bool
    foo _ 0 = True
    foo b n = foo b (n-1)
