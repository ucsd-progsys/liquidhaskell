{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--no-adt" @-}

module Step2 where

{-@ reflect sumListWith @-}
sumListWith :: [Int] -> Int -> Int
sumListWith []       c = c
sumListWith (c : cs) _ = sumListWith cs c

{-@ reflect sumList @-}
sumList :: [Int] -> Int
sumList cs = sumListWith cs 0
