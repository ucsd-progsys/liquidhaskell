{-# LANGUAGE GADTs #-}

{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--ple"            @-}

module Peano where

--------------------------------------------------------------------------------
-- | Peano Numbers -------------------------------------------------------------
--------------------------------------------------------------------------------

{-@ data Peano [toNat] @-}
data Peano where
  Z :: Peano
  S :: Peano -> Peano

{-@ measure toNat @-}
{-@ toNat :: Peano -> Nat @-}
toNat :: Peano -> Int
toNat Z     = 0
toNat (S n) = 1 + toNat n

{-@ reflect plus @-}
plus :: Peano -> Peano -> Peano
plus Z     n = n
plus (S m) n = S (plus m n)

{-@ reflect double @-}
double :: Peano -> Peano
double n = plus n n
