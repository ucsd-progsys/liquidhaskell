
module Implicit3 where

{-@ type IntN N = {v:Int | v = N} @-}

{-@ foo :: n:Int ~> (() -> IntN n) -> IntN {n+1} @-}
foo :: (() -> Int) -> Int
foo f = 1 + f ()

{-@ bar :: IntN 3 @-}
bar = foo (\_ -> foo (\_ -> 1))
