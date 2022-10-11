{-@ LIQUID "--expect-error-containing=Specified type does not refine Haskell type for `Inconsistent1.incr` (Checked)" @-}
module Inconsistent1 where

{-@ incr :: Int -> Bool @-}
incr :: Int -> Int 
incr x = x + 1
