-- | A simple depth test for `--eliminate`. The size of the max KInfo depth is
--   about 2x the number of calls to `incr`.
module ElimMonad (prop) where

{-@ prop :: x:Nat -> IO {v:Int | v = x + 22} @-}
prop :: Int -> IO Int
prop x = do
  x <- incr x
  x <- incr x
  x <- incr x
  x <- incr x
  x <- incr x
  x <- incr x
  x <- incr x
  x <- incr x
  x <- incr x
  x <- incr x
  x <- incr x
  x <- incr x
  x <- incr x
  x <- incr x
  x <- incr x
  x <- incr x
  x <- incr x
  x <- incr x
  x <- incr x
  x <- incr x
  x <- incr x
  x <- incr x
  return x

{-@ incr :: dog:Int -> IO {v:Int | v == dog + 1} @-}
incr :: Int -> IO Int
incr cat = return (cat + 1)
