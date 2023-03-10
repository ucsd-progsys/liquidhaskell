module spec GHC.Real where

import GHC.Types

(GHC.Real.^) :: (GHC.Num.Num a, GHC.Real.Integral b) => x:a -> y:{n:b | n >= 0} -> {z:a | (y == 0 => z == 1) && ((x == 0 && y /= 0) <=> z == 0)}

GHC.Real.fromIntegral    :: (GHC.Real.Integral a, GHC.Num.Num b) => x:a -> {v:b|v=x}

class (GHC.Num.Num a) => GHC.Real.Fractional a where
  (GHC.Real./)   :: x:a -> y:{v:a | v /= 0} -> {v:a | v == x / y}
  GHC.Real.recip :: a -> a
  GHC.Real.fromRational :: GHC.Real.Ratio Integer -> a

class (GHC.Real.Real a, GHC.Enum.Enum a) => GHC.Real.Integral a where
  GHC.Real.quot :: x:a -> y:{v:a | v /= 0} -> {v:a | (v = (x / y)) &&
                                                     ((x >= 0 && y >= 0) => v >= 0) &&
                                                     ((x >= 0 && y >= 1) => v <= x) }
  GHC.Real.rem :: x:a -> y:{v:a | v /= 0} -> {v:a | ((v >= 0) && (v < y))}
  GHC.Real.mod :: x:a -> y:{v:a | v /= 0} -> {v:a | v = x mod y && ((0 <= x && 0 < y) => (0 <= v && v < y))}

  GHC.Real.div :: x:a -> y:{v:a | v /= 0} -> {v:a | (v = (x / y)) &&
                                                    ((x >= 0 && y >= 0) => v >= 0) &&
                                                    ((x >= 0 && y >= 1) => v <= x) && 
                                                    ((1 < y)            => v < x ) && 
                                                    ((y >= 1)           => v <= x)  
                                                    }
  GHC.Real.quotRem :: x:a -> y:{v:a | v /= 0} -> ( {v:a | (v = (x / y)) &&
                                                          ((x >= 0 && y >= 0) => v >= 0) &&
                                                          ((x >= 0 && y >= 1) => v <= x)}
                                                 , {v:a | ((v >= 0) && (v < y))})
  GHC.Real.divMod :: x:a -> y:{v:a | v /= 0} -> ( {v:a | (v = (x / y)) &&
                                                         ((x >= 0 && y >= 0) => v >= 0) &&
                                                         ((x >= 0 && y >= 1) => v <= x) }
                                                , {v:a | v = x mod y && ((0 <= x && 0 < y) => (0 <= v && v < y))}
                                                )
  GHC.Real.toInteger :: x:a -> {v:Integer | v = x}

//  fixpoint can't handle (x mod y), only (x mod c) so we need to be more clever here
//  mod :: x:a -> y:a -> {v:a | v = (x mod y) }
