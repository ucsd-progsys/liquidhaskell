
module List04 where

{-@ data L [llen] @-}
data L a = N | C a (L a)

{-@ measure llen @-}
{-@ llen :: (L a) -> Nat @-}
llen :: (L a) -> Int
llen N        = 0
llen (C x xs) = 1 + llen xs 

rev               = go N 

{-@ go :: _ -> xs:_ -> _ / [llen xs] @-}  
go acc N        = acc
go acc (C x xs) = go (C x acc) xs

