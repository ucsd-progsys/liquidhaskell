module DeltaSort where

import           Prelude                 hiding ( abs
                                                , max
                                                )

sort :: [Int] -> [Int]
sort []       = []
sort (x : xs) = sort (filter (< x) xs) ++ [x] ++ sort (filter (>= x) xs)

{-@ reflect delta @-}
{-@ delta :: xs:[Int] -> {ys:[Int]|len ys = len xs} -> Int @-}
delta :: [Int] -> [Int] -> Int
delta []       []       = 0
delta (x : xs) (y : ys) = max (abs (x - y)) (delta xs ys)

{-@ relational sort ~ sort :: {xs:[Int] -> [Int] ~ ys:[Int] -> [Int]
                           | true :=> DeltaSort.delta xs ys >= DeltaSort.delta (r1 xs) (r2 ys)} @-}

---------------------
------- Utils -------
---------------------

{-@ reflect max @-}
max :: Int -> Int -> Int
max a b = if a < b then b else a

{-@ reflect abs @-}
abs :: Int -> Int
abs x = if x < 0 then -x else x
