module Ignores where

{-@ ignore inc @-}
{-@ inc :: Nat -> Nat @-}
inc :: Int -> Int 
inc x = x - 1 

