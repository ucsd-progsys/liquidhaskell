module LocalSpec0 (foo) where


{-@ foo :: x:Int -> {v:Int | v > x } @-}
foo :: Int -> Int
foo x =  go x
  where
    {-@ go :: n:Int -> {v:Int | v = n + 1} @-}
    go :: Int -> Int
    go x = x + 1
