{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
module GHC.Float_LHAssumptions(Floating(..)) where

{-@
class (GHC.Real.Fractional a) => GHC.Float.Floating a where
  GHC.Float.pi       :: a
  GHC.Float.exp      :: a -> {y:a | y > 0}
  GHC.Float.log      :: {x:a | x > 0} -> a
  GHC.Float.sqrt     :: {x:a | x >= 0} -> {y:a | y >= 0}
  (GHC.Float.**)     :: x:a -> {y:a | x = 0 => y >= 0} -> a
  GHC.Float.logBase  :: {b:a | b > 0 && b /= 1} -> {x:a | x > 0} -> a
  GHC.Float.sin      :: a -> {y:a | -1 <= y && y <= 1}
  GHC.Float.cos      :: a -> {y:a | -1 <= y && y <= 1}
  GHC.Float.tan      :: a -> a
  GHC.Float.asin     :: {x:a | -1 <= x && x <= 1} -> a
  GHC.Float.acos     :: {x:a | -1 <= x && x <= 1} -> a
  GHC.Float.atan     :: a -> a
  GHC.Float.sinh     :: a -> a
  GHC.Float.cosh     :: a -> {y:a | y >= 1}
  GHC.Float.tanh     :: a -> {y:a | -1 < y && y < 1}
  GHC.Float.asinh    :: a -> a
  GHC.Float.acosh    :: {y:a | y >= 1} -> a
  GHC.Float.atanh    :: {y:a | -1 < y && y < 1} -> a
  GHC.Float.log1p    :: a -> a
  GHC.Float.expm1    :: a -> a
  GHC.Float.log1pexp :: a -> a
  GHC.Float.log1mexp :: a -> a
@-}
