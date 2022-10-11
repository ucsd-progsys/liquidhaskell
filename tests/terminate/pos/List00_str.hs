
module List00_str where

lmap f []     = []
lmap f (x:xs) = f x : lmap f xs

lref = go [] 
  where
    go acc [] = acc 
    go acc (x:xs) = go (x:acc) xs 
