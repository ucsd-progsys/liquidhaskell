-- | A "client" that uses the reflected definitions.

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-} 

module Lists where

import Prelude hiding (concat, filter, foldr, map)

{-@ reflect incr @-}
incr :: Int -> Int
incr x = x + 1

{-@ reflect isPos @-}
isPos :: Int -> Bool 
isPos x = x > 0 

{-@ reflect ints0 @-}
ints0 :: [Int] 
ints0 = [0, 1, 2] 

{-@ reflect ints1 @-}
ints1 :: [Int] 
ints1 = [1, 2, 3] 

{-@ reflect ints2 @-}
ints2 :: [Int] 
ints2 = [1, 2] 

{-@ mapProp :: () -> { map incr ints0 == ints1 } @-}
mapProp () = ()

{-@ filterProp :: () -> { filter isPos ints0 == ints2 } @-}
filterProp () = ()

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


