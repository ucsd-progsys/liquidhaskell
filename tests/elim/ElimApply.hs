-- | A simple depth test for `--eliminate`. The size of the max KInfo depth is
--   about 2x the number of calls to `incr`.
module ElimMonad (prop) where

{-@ prop :: x:Nat -> {v:Int | v = x + 30} @-}
prop :: Int -> Int
prop x = incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr
       $ incr x

{-@ incr :: dog:Int -> {v:Int | v == dog + 1} @-}
incr :: Int -> Int
incr cat = cat + 1
