module spec GHC.Num where

// embed GHC.Integer.Type.Integer as int 

GHC.Num.fromInteger :: (GHC.Num.Num a) => x:_ -> {v:a | v = x }

GHC.Num.negate :: (GHC.Num.Num a)
               => x:a
               -> {v:a | v = -x}
