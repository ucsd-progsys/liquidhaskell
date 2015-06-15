module Blank (foo) where

-- This is a blank file.

data G = A | B

{-@ foo :: Int -> {v:G | v = A} @-}
foo  :: Int -> G
foo _ = B


