{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}

module Basics where

{-@ data Peano [toNat] = O | S Peano @-}
data Peano = O | S Peano

{-@ measure toNat @-}
{-@ toNat :: Peano -> Nat @-}
toNat :: Peano -> Int
toNat O     = 0
toNat (S n) = 1 + toNat n

{-@ reflect evn @-}
evn :: Peano -> Bool
evn O         = True
evn (S O)     = False
evn (S (S n)) = evn n

{-@ reflect plus @-}
plus :: Peano -> Peano -> Peano
plus O     n = n
plus (S m) n = S (plus m n)

