module spec GHC.Real where

GHC.Real.div             :: (GHC.Real.Integral a) => x:a -> y:a -> {v:a | ((v = (x / y)) && (((x>=0) && (y>=0)) => (v>=0)) && (((x>=0) && (y>=1)) => (v<=x))) }
GHC.Real.quotRem         :: (GHC.Real.Integral a) => x:a -> y:a -> ({v:a | ((v = (x / y)) && (((x>=0) && (y>=0)) => (v>=0)) && (((x>=0) && (y>=1)) => (v<=x)))}
                                                                 ,{v:a | ((v >= 0) && (v < y))})

-- fixpoint can't handle (x mod y), only (x mod c) so we need to be more clever here
-- GHC.Real.mod             :: (Integral a) => x:a -> y:a -> {v:a | v = (x mod y) }
GHC.Real./               :: (GHC.Real.Fractional a) => x:a -> y:{v:a | v != 0} -> {v: a | v = (x / y) }

GHC.Real.toInteger       :: (GHC.Real.Integral a) => x:a -> {v:GHC.Integer.Type.Integer | v = x}
GHC.Real.fromIntegral    :: (GHC.Real.Integral a, GHC.Num.Num b) => x:a -> {v:b|v=x}

