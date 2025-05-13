{-# OPTIONS_GHC -Wno-unused-imports #-}
-- | This is an instance of LiquidHaskell having a flat import namespace
-- for logic names. Here, both Nat modules define the same type alias 'INat',
-- producing an error even though we explicitly qualify it to avoid ambiguity.
module Length where

import qualified Nat1 as N
import Nat2

{-@ llength :: [a] -> Nat @-}
llength :: [a] -> Int
llength [] = 0
llength (x:xs) = 1 + length xs
