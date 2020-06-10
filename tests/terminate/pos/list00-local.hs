
module List00_Local where

lrev :: [a] -> [a]
lrev = go [] 
  where  
    {-@ go :: _ -> xs:_ -> _ / [len xs] @-}
    go :: [a] -> [a] -> [a]
    go acc []     = acc 
    go acc (x:xs) = go (x:acc) xs 
