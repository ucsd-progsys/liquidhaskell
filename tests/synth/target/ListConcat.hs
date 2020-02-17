{-@ LIQUID "--typed-holes" @-}

module ListConcat where

{-@ measure length' @-}
{-@ length' :: [a] -> Nat @-}
length' :: [a] -> Int
length' []     = 0
length' (x:xs) = 1 + length' xs

{-@ measure sumLen @-}
{-@ sumLen :: [[a]] -> Nat @-}
sumLen :: [[a]] -> Int
sumLen []     = 0
sumLen (x:xs) = length' x + sumLen xs

{-@ append0 :: xs: [a] -> ys: [a] -> {v: [a] | length' v == length' xs + length' ys} @-}
append0 :: [a] -> [a] -> [a]
append0 []     ys = ys
append0 (x:xs) ys = x:append0 xs ys

{-@ concat0 :: x: [[a]] -> { v: [a] | length' v == sumLen x } @-}
concat0 :: [[a]] -> [a]
concat0 = _goal
-- concat0 x = 
--     case x of
--         []    -> []
--         x3:x4 -> append0 x3 (concat0 x4)
