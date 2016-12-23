module Holes (incr) where

{-@ incr :: Nat -> {v:_ | _ } @-}
incr :: Int -> Int
incr x = x + 1
