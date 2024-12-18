{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
-- Reexports are necessary for LH to expose specs of type classes
module GHC.Real_LHAssumptions(Integral(..), Fractional(..)) where

import GHC.Real
import GHC.Types_LHAssumptions()

{-@
assume (^) :: x:a -> y:{n:b | n >= 0} -> {z:a | (y == 0 => z == 1) && ((x == 0 && y /= 0) <=> z == 0)}

assume fromIntegral    :: x:a -> {v:b|v=x}

class Num a => Fractional a where
  (/)   :: x:a -> y:{v:a | v /= 0} -> {v:a | v == x / y}
  recip :: a -> a
  fromRational :: Ratio Integer -> a

class (Real a, Enum a) => Integral a where
  quot :: x:a -> y:{v:a | v /= 0} -> {v:a | (v = (x / y)) &&
                                                     ((x >= 0 && y >= 0) => v >= 0) &&
                                                     ((x >= 0 && y >= 1) => v <= x) }
  rem :: x:a -> y:{v:a | v /= 0} -> {v:a | ((v >= 0) && (v < y))}
  mod :: x:a -> y:{v:a | v /= 0} -> {v:a | v = x mod y && ((0 <= x && 0 < y) => (0 <= v && v < y))}

  div :: x:a -> y:{v:a | v /= 0} -> {v:a | (v = div x y) &&
                                                    ((x >= 0 && y >= 0) => v >= 0) &&
                                                    ((x >= 0 && y >= 1) => v <= x) &&
                                                    ((1 < y && x >= 0)  => v < x) &&
                                                    ((1 < y && x < 0)   => v > x) &&
                                                    ((y >= 1 && x >= 0)  => v <= x) &&
                                                    ((x < 0 && y > 0)   => v <= 0) &&
                                                    ((x > 0 && y < 0)   => v <= 0) &&
                                                    ((x < 0 && y < 0)   => v >= 0)
                                                    }
  quotRem :: x:a -> y:{v:a | v /= 0} -> ( {v:a | (v = (x / y)) &&
                                                          ((x >= 0 && y >= 0) => v >= 0) &&
                                                          ((x >= 0 && y >= 1) => v <= x)}
                                                 , {v:a | ((v >= 0) && (v < y))})
  divMod :: x:a -> y:{v:a | v /= 0} -> ( {v:a | (v = (x / y)) &&
                                                         ((x >= 0 && y >= 0) => v >= 0) &&
                                                         ((x >= 0 && y >= 1) => v <= x) }
                                                , {v:a | v = x mod y && ((0 <= x && 0 < y) => (0 <= v && v < y))}
                                                )
  toInteger :: x:a -> {v:Integer | v = x}

//  fixpoint can't handle (x mod y), only (x mod c) so we need to be more clever here
//  mod :: x:a -> y:a -> {v:a | v = (x mod y) }
@-}
