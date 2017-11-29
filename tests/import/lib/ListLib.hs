-- | A module with some definitions for Lists

{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--higherorder" @-}

module ListLib where

import Prelude hiding (concat, filter, foldr, map)

{-@ reflect map @-}
map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x : map f xs

{-@ reflect filter @-}
filter :: (a -> Bool) -> [a] -> [a]
filter f []     = []
filter f (x:xs) = if f x then x : filter f xs else filter f xs

{-@ reflect append @-}
append :: [a] -> [a] -> [a]
append []     ys = ys
append (x:xs) ys = x : append xs ys

{-@ reflect concat @-}
concat :: [[a]] -> [a]
concat []     = []
concat (l:ls) = append l (concat ls)

{-@ reflect foldr @-}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f i [ ]    = i
foldr f i (x:xs) = f x (foldr f i xs)
