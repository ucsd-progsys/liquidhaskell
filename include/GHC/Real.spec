module spec GHC.Real where

(GHC.Real.^) :: (GHC.Num.Num a, GHC.Real.Integral b) => a:a -> n:b -> {v:a | v == 0 <=> a == 0 }

GHC.Real.fromIntegral    :: (GHC.Real.Integral a, GHC.Num.Num b) => x:a -> {v:b|v=x}

class (GHC.Num.Num a) => GHC.Real.Fractional a where
  (GHC.Real./)   :: x:a -> y:{v:a | v /= 0} -> {v:a | v == x / y}
  GHC.Real.recip :: a -> a
  GHC.Real.fromRational :: GHC.Real.Rational -> a

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
  GHC.Real.toInteger :: x:a -> {v:GHC.Integer.Type.Integer | v = x}

// fixpoint can't handle (x mod y), only (x mod c) so we need to be more clever here
// mod :: x:a -> y:a -> {v:a | v = (x mod y) }
