{-@ LIQUID "--expect-any-error" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module T1409 where

data Peano = Z | S Peano

{-@ reflect isEven @-}
isEven :: Peano -> Bool
isEven Z     = True
isEven (S n) = not (isEven n)

{-@ foo :: _ -> {v:Int | v = 0} @-}
foo :: Peano -> Int
foo (S Z) = 5
foo _     = 0
