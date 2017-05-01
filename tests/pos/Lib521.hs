module Lib521 where

{-@ measure size @-}
{-@ size    :: xs:[a] -> {v:Nat | v = size xs} @-}
size :: [a] -> Int
size []     = 0
size (_:rs) = 1 + size rs
