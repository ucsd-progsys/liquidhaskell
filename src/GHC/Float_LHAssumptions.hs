{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module GHC.Float_LHAssumptions(Floating(..)) where

import GHC.Float

{-@
class Fractional a => Floating a where
  pi       :: a
  exp      :: a -> {y:a | y > 0}
  log      :: {x:a | x > 0} -> a
  sqrt     :: {x:a | x >= 0} -> {y:a | y >= 0}
  (**)     :: x:a -> {y:a | x = 0 => y >= 0} -> a
  logBase  :: {b:a | b > 0 && b /= 1} -> {x:a | x > 0} -> a
  sin      :: a -> {y:a | -1 <= y && y <= 1}
  cos      :: a -> {y:a | -1 <= y && y <= 1}
  tan      :: a -> a
  asin     :: {x:a | -1 <= x && x <= 1} -> a
  acos     :: {x:a | -1 <= x && x <= 1} -> a
  atan     :: a -> a
  sinh     :: a -> a
  cosh     :: a -> {y:a | y >= 1}
  tanh     :: a -> {y:a | -1 < y && y < 1}
  asinh    :: a -> a
  acosh    :: {y:a | y >= 1} -> a
  atanh    :: {y:a | -1 < y && y < 1} -> a
  log1p    :: a -> a
  expm1    :: a -> a
  log1pexp :: a -> a
  log1mexp :: a -> a
@-}
