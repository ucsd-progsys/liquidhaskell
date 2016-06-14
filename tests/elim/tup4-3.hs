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

    t2 = (\z1 -> case t1 of 
                   Pair y2 y2' -> Pair y2 y2')
         () 

    t3 = (\z1 -> case t2 of 
                   Pair y3 y3' -> Pair y3 y3')
         () 

    Pair aga maga = t3
