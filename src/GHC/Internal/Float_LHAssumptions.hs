{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
module GHC.Internal.Float_LHAssumptions(Floating(..)) where

{-@
class (GHC.Internal.Real.Fractional a) => GHC.Internal.Float.Floating a where
  GHC.Internal.Float.pi       :: a
  GHC.Internal.Float.exp      :: a -> {y:a | y > 0}
  GHC.Internal.Float.log      :: {x:a | x > 0} -> a
  GHC.Internal.Float.sqrt     :: {x:a | x >= 0} -> {y:a | y >= 0}
  (GHC.Internal.Float.**)     :: x:a -> {y:a | x = 0 => y >= 0} -> a
  GHC.Internal.Float.logBase  :: {b:a | b > 0 && b /= 1} -> {x:a | x > 0} -> a
  GHC.Internal.Float.sin      :: a -> {y:a | -1 <= y && y <= 1}
  GHC.Internal.Float.cos      :: a -> {y:a | -1 <= y && y <= 1}
  GHC.Internal.Float.tan      :: a -> a
  GHC.Internal.Float.asin     :: {x:a | -1 <= x && x <= 1} -> a
  GHC.Internal.Float.acos     :: {x:a | -1 <= x && x <= 1} -> a
  GHC.Internal.Float.atan     :: a -> a
  GHC.Internal.Float.sinh     :: a -> a
  GHC.Internal.Float.cosh     :: a -> {y:a | y >= 1}
  GHC.Internal.Float.tanh     :: a -> {y:a | -1 < y && y < 1}
  GHC.Internal.Float.asinh    :: a -> a
  GHC.Internal.Float.acosh    :: {y:a | y >= 1} -> a
  GHC.Internal.Float.atanh    :: {y:a | -1 < y && y < 1} -> a
  GHC.Internal.Float.log1p    :: a -> a
  GHC.Internal.Float.expm1    :: a -> a
  GHC.Internal.Float.log1pexp :: a -> a
  GHC.Internal.Float.log1mexp :: a -> a
@-}
