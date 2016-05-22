module Foo where

{-@ bar :: Nat -> Nat @-}
bar :: Int -> Int
bar thing = aga + maga
  where
    t1 = (\z1 -> let mickey = z1
                     y1      = mickey
                     y1'     = mickey + 1
                 in (y1, y1')) thing

    t2 = (\z2 -> let y2  = fst t1
                     y2' = snd t1
                 in (y2, y2')) ()

    t3 = (\z3 -> let y3  = fst t2
                     y3' = snd t2
                 in (y3, y3') ) ()

    aga  = fst t3
    maga = snd t3


