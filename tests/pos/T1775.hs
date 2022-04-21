module T1775 where

{-@ measure listLength @-}
{-@ listLength :: xs:_ -> {n:Nat | n == len xs } @-}
listLength :: [a] -> Int
listLength [] = 0
listLength (_x:xs) = 1 + listLength xs

{-@ foo :: xs:_ -> {ys:_ | listLength xs == len ys } @-}
foo :: [a] -> [a]
foo xs =  xs
