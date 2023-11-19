{-@ LIQUID "--expect-error-containing=> 5}" @-}
module SplitSubtype where

{-@ foo :: {v:Int | v > 0 && v > 5 && v < 10 } -> Int @-}
foo :: Int -> Int
foo x = x + 1

bar = foo 2 
-- We want to see the error pinpointed to the second conjunct.
