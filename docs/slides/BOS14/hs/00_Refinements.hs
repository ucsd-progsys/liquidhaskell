{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-warnings" @-}

module Poo where

import Prelude hiding (map, foldr, foldr1)


-- wtAverage :: [(Int, Int)] -> Int

divide    :: Int -> Int -> Int
divide n 0 = dead "div by zero"
divide n k = n `div` k


{-@ dead :: {v:_ | false} -> a @-}
dead msg = error msg




{-@ type Nat = {v:Int | v >= 0} @-}
{-@ type Pos = {v:Int | v >  0} @-}




{-@ divide :: Int -> Pos -> Int @-}
divide x 0 = dead "divide-by-zero"
divide x n = x `div` n




{-@ boo :: Int -> Nat -> Int @-}
boo x y    = divide x (y + 1)


-- {- wtAverage :: {v : [(Pos, Pos)] | len v > 0} -> Int @-}
-- wtAverage wxs = total `div` weights
--   where
--     total     = sum [ w * x | (w, x) <- wxs ]
--     weights   = sum [ w     | (w, _) <- wxs ]
--     sum       = foldr1 (+)
-- 
-- 

data List a = N | C a (List a)

map f (N)      = N
map f (C x xs) = C (f x) (map f xs) 




foldr f acc N        = acc
foldr f acc (C x xs) = f x (foldr f acc xs)
