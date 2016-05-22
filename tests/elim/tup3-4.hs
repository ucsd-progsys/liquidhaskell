module Foo where

import Prelude hiding (fst, snd)

data Pair a b = Pair {fst :: a, snd :: b} 

{-@ bar :: Nat -> Nat @-}
bar :: Int -> Int
bar thing = aga + maga
  where
    t1 = (\z1 -> let mickey = z1
                     y1      = mickey
                     y1'     = mickey + 1
                 in Pair y1 y1') thing

    t2 = (\z2 -> let y2  = fst t1
                     y2' = snd t1
                 in Pair y2 y2') ()

    t3 = (\z3 -> let y3  = fst t2
                     y3' = snd t2
                 in Pair y3 y3') ()

    t4 = (\z4 -> let y4  = fst t3
                     y4' = snd t3
                 in Pair y4 y4') ()

    aga  = fst t4
    maga = snd t4

{-
bar :: Int -> Int
bar n =
  let e = (n, (n+1, n+2)) in
  case e of
    (x, (y, z)) -> x + y + z
-}
