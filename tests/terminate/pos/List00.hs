
module List00 where

lmap f []     = []
lmap f (x:xs) = f x : lmap f xs

lref = go [] 
 
{-@ go :: _ -> xs:_ -> _ / [len xs] @-}
go acc []     = acc 
go acc (x:xs) = go (x:acc) xs 

lmapFlipped [] f     = []
lmapFlipped (x:xs) f = f x : lmapFlipped xs f

lrefFlipped = (\x -> goFlipped x [])

{-@ goFlipped :: xs:_ -> _ -> _ / [len xs] @-}
goFlipped [] acc = acc
goFlipped (x:xs) acc = goFlipped xs (x:acc)
