{-# LANGUAGE GADTs #-}

{-@ LIQUID "--typeclass" @-}
module ConstrainedGADT where

class C a where
  c :: a -> a

-- `Box` is an ordinary GADT constructor, not a class dictionary constructor.
-- Its GHC constructor signature nevertheless has a `C a` dictionary constraint.
data Box a where
  Box :: C a => a -> Box a

{-@ data Box a where
      Box :: a -> Box a
  @-}

box :: C a => a -> Box a
box = Box

unbox :: Box a -> a
unbox (Box x) = x
