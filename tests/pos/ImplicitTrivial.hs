module ImplicitTrivial where

-- This module has implicits but doesn't acutally use them for verification

{-@ foo :: n:Int ~> m:Int -> {v:_|v=m+1} @-}
foo :: Int -> Int
foo moo = 1 + moo

{-@ bar :: o:Int -> {v:_|v=o+1} @-}
bar :: Int -> Int
bar goo = foo goo
