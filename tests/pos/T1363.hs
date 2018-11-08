{-# LANGUAGE BangPatterns #-}
{-@ LIQUID "--exact-data-cons" @-}

{-@ mySum :: Integer -> xs:[Integer] -> Integer / [len xs] @-}
mySum :: Integer -> [Integer] -> Integer
mySum z []     = z
mySum z (x:xs) = mySum (z + x) xs

{-@ reflect mySum @-}

{-@ mySum' :: Integer -> xs:[Integer] -> Integer / [len xs] @-}
mySum' :: Integer -> [Integer] -> Integer
mySum' z []     = z
mySum' z (x:xs) = let !z' = z + x 
                  in mySum' z' xs

{-@ reflect mySum' @-}