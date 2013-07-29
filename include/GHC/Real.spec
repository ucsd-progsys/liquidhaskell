module spec GHC.Real where

assume GHC.Real.div             :: (Integral a) => x:a -> y:a -> {v:a | ((v = (x / y)) && (((x>=0) && (y>=0)) => (v>=0)) && (((x>=0) && (y>=1)) => (v<=x))) }
assume GHC.Real.quotRem         :: (Integral a) => x:a -> y:a -> ({v:a | ((v = (x / y)) && (((x>=0) && (y>=0)) => (v>=0)) && (((x>=0) && (y>=1)) => (v<=x)))}
                                                                 ,{v:a | ((v >= 0) && (v < y))})

-- fixpoint can't handle (x mod y), only (x mod c) so we need to be more clever here
-- assume GHC.Real.mod             :: (Integral a) => x:a -> y:a -> {v:a | v = (x mod y) }
assume GHC.Real./               :: (Fractional a) => x:a -> y:{v:a | v != 0} -> {v: a | v = (x / y) }

assume GHC.Real.toInteger       :: (Integral a) => x:a -> {v:Integer | v = x}
assume GHC.Real.fromIntegral    :: (Integral a, Num b) => x:a -> {v:b|v=x}

