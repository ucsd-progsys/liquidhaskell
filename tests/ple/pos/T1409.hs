{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module T1409 where

data Peano = Z | S Peano

{-@ reflect isEven @-}
isEven :: Peano -> Bool
isEven Z     = True
-- isEven (S Z) = False                 --- adding this line makes the code pass
isEven (S n) = not (isEven n)

{-@ foo :: n:{ isEven n } -> {v:Int | v = 0} @-}
foo :: Peano -> Int
foo (S Z) = 5
foo _     = 0
