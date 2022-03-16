{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

module Language.Stitch.LH.Data.Nat where

import Prelude hiding (max)

{-@ type Nat = { v : Int | v >= 0 } @-}
type Nat = Int

{-@ inline max @-}
max :: Ord a => a -> a -> a
max a b = if a > b then a else b

{-@ inline minus @-}
minus :: Nat -> Nat -> Nat
minus a b = max 0 (a - b)
