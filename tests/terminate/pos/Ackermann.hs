module Ackermann where

data Peano = Z | S Peano

ack :: Peano -> Peano -> Peano
ack Z n = S n
ack (S m) Z = ack m (S Z)
ack sm@(S m) (S n) = ack m (ack sm n)

ackFlipped :: Peano -> Peano -> Peano
ackFlipped n Z = S n
ackFlipped Z (S m) = ackFlipped (S Z) m
ackFlipped (S n) sm@(S m) = ackFlipped (ackFlipped n sm) m

-- This case is redundant, but without it LH can't determine that this function
-- is total. See https://github.com/ucsd-progsys/liquidhaskell/issues/1396
-- Commenting out this case because termination breaks with -fdefer-typed-holes on 
{-@ LIQUID "--no-totality" @-}
-- ackFlipped _ _ = error "unreachable"

