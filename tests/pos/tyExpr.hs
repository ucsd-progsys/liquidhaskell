module Foo where

{-@ type Range Lo Hi = {v:Int | Lo <= v && v < Hi} @-}

{-@ bow :: Range 0 100 @-}
bow :: Int
bow = 12
