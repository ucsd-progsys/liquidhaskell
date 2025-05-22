-- |

module QuotRem where

{-@ predicate EqSign X Y = if X >= 0 then Y >= 0 else Y < 0 @-}

{-@ quotRemProps :: x:a
                    -> {y:a | y /= 0 && EqSign x y}
                    -> {z : (a,a) |
                         (EqSign x y => fst z = x / y && snd z = x mod y)}  @-}
quotRemProps :: Integral a => a -> a -> (a,a)
quotRemProps x y = (div x y, mod x y)
