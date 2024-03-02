{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
-- Reexports are necessary for LH to expose specs of type classes
module GHC.Real_LHAssumptions(Integral(..), Fractional(..)) where

import GHC.Types_LHAssumptions()

{-@
assume (GHC.Internal.Real.^) :: x:a -> y:{n:b | n >= 0} -> {z:a | (y == 0 => z == 1) && ((x == 0 && y /= 0) <=> z == 0)}

assume GHC.Internal.Real.fromIntegral    :: x:a -> {v:b|v=x}

class (GHC.Internal.Num.Num a) => GHC.Internal.Real.Fractional a where
  (GHC.Internal.Real./)   :: x:a -> y:{v:a | v /= 0} -> {v:a | v == x / y}
  GHC.Internal.Real.recip :: a -> a
  GHC.Internal.Real.fromRational :: GHC.Internal.Real.Ratio Integer -> a

class (GHC.Internal.Real.Real a, GHC.Internal.Enum.Enum a) => GHC.Internal.Real.Integral a where
  GHC.Internal.Real.quot :: x:a -> y:{v:a | v /= 0} -> {v:a | (v = (x / y)) &&
                                                     ((x >= 0 && y >= 0) => v >= 0) &&
                                                     ((x >= 0 && y >= 1) => v <= x) }
  GHC.Internal.Real.rem :: x:a -> y:{v:a | v /= 0} -> {v:a | ((v >= 0) && (v < y))}
  GHC.Internal.Real.mod :: x:a -> y:{v:a | v /= 0} -> {v:a | v = x mod y && ((0 <= x && 0 < y) => (0 <= v && v < y))}

  GHC.Internal.Real.div :: x:a -> y:{v:a | v /= 0} -> {v:a | (v = (x / y)) &&
                                                    ((x >= 0 && y >= 0) => v >= 0) &&
                                                    ((x >= 0 && y >= 1) => v <= x) && 
                                                    ((1 < y)            => v < x ) && 
                                                    ((y >= 1)           => v <= x)  
                                                    }
  GHC.Internal.Real.quotRem :: x:a -> y:{v:a | v /= 0} -> ( {v:a | (v = (x / y)) &&
                                                          ((x >= 0 && y >= 0) => v >= 0) &&
                                                          ((x >= 0 && y >= 1) => v <= x)}
                                                 , {v:a | ((v >= 0) && (v < y))})
  GHC.Internal.Real.divMod :: x:a -> y:{v:a | v /= 0} -> ( {v:a | (v = (x / y)) &&
                                                         ((x >= 0 && y >= 0) => v >= 0) &&
                                                         ((x >= 0 && y >= 1) => v <= x) }
                                                , {v:a | v = x mod y && ((0 <= x && 0 < y) => (0 <= v && v < y))}
                                                )
  GHC.Internal.Real.toInteger :: x:a -> {v:Integer | v = x}

//  fixpoint can't handle (x mod y), only (x mod c) so we need to be more clever here
//  mod :: x:a -> y:a -> {v:a | v = (x mod y) }
@-}
