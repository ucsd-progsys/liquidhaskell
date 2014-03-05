module Blank (foo) where

-- This is a blank file.

data G = A | B

{-@ foo :: {v:Int | true} -> {v:G | v = B} @-}
foo  :: Int -> G
foo _ = A
