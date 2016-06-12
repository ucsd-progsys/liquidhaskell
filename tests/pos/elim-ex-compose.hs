module ElimExCompose (prop) where

{-@ prop :: x:Nat -> {v:Int | v = x + 5} @-}
prop :: Int -> Int
prop = incr . incr . incr . incr . incr

{-@ incr :: dog:Int -> {v:Int | v == dog + 1} @-}
incr :: Int -> Int
incr cat = cat + 1
