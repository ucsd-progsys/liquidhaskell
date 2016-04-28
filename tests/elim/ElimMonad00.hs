-- | A simple depth test for `--eliminate`. The size of the max KInfo depth is
--   about 2x the number of calls to `incr`.
module ElimMonad (prop) where

{-@ prop :: x:Nat -> IO {v:Int | v = x + 3} @-}
prop :: Int -> IO Int
prop apple = do
  banana  <- incr apple
  cherry  <- incr banana
  falafel <- incr cherry
  return falafel 

{-@ incr :: dog:Int -> IO {v:Int | v == dog + 1} @-}
incr :: Int -> IO Int
incr cat = return (cat + 1)
