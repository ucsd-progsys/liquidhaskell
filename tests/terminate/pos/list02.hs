-- module TestRec (llen) where
-- import Prelude hiding (map, foldl)

module List02 where

data L a = N | C a (L a)

{-@ data L [llen] @-}

{-@ measure llen @-}
{-@ llen :: (L a) -> Nat @-}
llen :: (L a) -> Int
llen N        = 0
llen (C x xs) = 1 + llen xs 

mapL f N = N
mapL f (C x xs) = C (f x) (mapL f xs)
