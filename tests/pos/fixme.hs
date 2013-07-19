module Fixme where

bar = go
  where go [] [] = []
        go (x:xs) [] = x:go xs []


{-@ Decrease go 2 @-}
baz = go
  where go [] [] = []
        go [] (x:xs) = x:go [] xs
