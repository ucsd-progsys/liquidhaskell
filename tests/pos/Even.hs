module Even where

{-@ notEven :: Int -> Even @-}
notEven :: Int -> Int
notEven x = x * 2
