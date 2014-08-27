module TestRec () where

import Prelude hiding (map, foldl)

data L a = N | C a (L a)
{-@ 
data L [llen] a = N | C (x::a) (xs::(L a))
  @-}

{-@ measure llen :: (L a) -> Int
    llen(N) = 0
    llen(C x xs) = 1 + (llen xs)
  @-}


{-@ map :: (a -> b) -> [a] -> [b]@-}
map f []     = []
map f (x:xs) = f x : map f (x:xs)
 
-- bar = map id []

{-@ Decrease go 2 @-}
rev xs = go [] xs
  where go ack  []    = ack
        go ack (x:xs) = go (x:ack) xs


mapL f N = N
mapL f (C x xs) = C (f x) (mapL f xs)
