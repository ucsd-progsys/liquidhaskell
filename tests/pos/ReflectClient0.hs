module ReflectClient0 where

import ReflectLib0

{-@ incr :: x:Nat -> {v:Nat | greaterThan x v } @-}
incr :: Int -> Int
incr x = x + 1
