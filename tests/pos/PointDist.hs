{-@ LIQUID "--short-names"    @-}

module Point where

-- | Non-negative numbers:

{-@ type NonNeg  = {v:Double | v >= 0.0 } @-}

-- | Non-negative, and zero iff X is zero:

{-@ type PosZ X  = {v:NonNeg | X == 0.0 <=> v == 0.0 } @-}
 
-- | The distance function, STATICALLY guaranteed to satisfy "pre/post"
--   or type spec, assuming no run-time checks fail

{-@ dist                 :: p1:Point -> p2:Point -> {v:NonNeg | v == 0.0 <=> EqPoint p1 p2} @-}
dist (P x1 y1) (P x2 y2) = d
  where 
    d                    = root   (dx + dy)
    dx                   = square (x1 - x2)
    dy                   = square (y1 - y2)

-- | A Data Type for Points

data Point = P { px :: Double, py::Double }

{-@ data Point = P { px :: Double, py :: Double } @-}

-- | When are two points "equal" ?

{-@ predicate EqPoint P1 P2 = (px P1 == px P2 && py P1 == py P2) @-}
                
-- | Squaring numbers: DYNAMIC checks establish numerical properties

{-@ square :: x:Double -> PosZ x @-}
square   :: Double -> Double
square 0 = 0
square x = assume (xx > 0) xx 
  where
    xx   = x * x

{-@ root :: x:NonNeg -> PosZ x  @-}
root :: Double -> Double
root 0  = 0
root x  = assume (rx > 0) rx
  where
    rx  = sqrt x

-- | Run-time Checks

{-@ assume     :: b:_ -> a -> {v:a | Prop b} @-}
assume True  x = x
assume False _ = error "Failed Dynamic Check!"


