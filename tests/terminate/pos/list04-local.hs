
module List04_local where

{-@ data L [llen] @-}
data L a = N | C a (L a)

{-@ measure llen @-}
{-@ llen :: (L a) -> Nat @-}
llen :: L a -> Int
llen N        = 0
llen (C x xs) = 1 + llen xs 

rev               = go N 
  where 
    {-@ go :: _ -> xs:_ -> _ / [llen xs] @-}  
    go :: L a -> L a -> L a  ----------------- >>> We need this GHC-tysig, maybe because the CORE is weird otherwise?
    go acc N        = acc
    go acc (C x xs) = go (C x acc) xs

