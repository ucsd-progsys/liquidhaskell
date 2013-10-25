module Goo (poop) where

class Zog a where
  zoom :: a -> Int

-- Assume the relevant behavior for the method.
{-@ zoom :: (Zog a) => a -> Nat @-}

-- Uses the behavior of `zoom`
{-@ poop :: (Zog a) => a -> Nat @-}
poop x = zoom x
