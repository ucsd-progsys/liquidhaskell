
lmap f []     = []
lmap f (x:xs) = f x : lmap f xs

lref = go [] 
 
{-@ go :: _ -> xs:_ -> _ / [len xs] @-}
go acc []     = acc 
go acc (x:xs) = go (x:acc) xs 
