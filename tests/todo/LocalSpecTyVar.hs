module LocalSpecTyVar where

foo = go
  where
    {-@ go :: xs:[a] -> {v:[a] | (len v) = (len xs)} @-}
    go []     = []
    go (x:xs) = x : go xs
