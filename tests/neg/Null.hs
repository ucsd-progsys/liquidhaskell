{-@ LIQUID "--expect-any-error" @-}
module Null where

foo :: [Int] -> Int
foo xs = if null xs then head xs else 0
