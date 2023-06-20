
module List05_local where

rev = go []
  where
    go :: [a] -> [a] -> [a]
    go acc []     = acc
    go acc (x:xs) = go (x:acc) xs
