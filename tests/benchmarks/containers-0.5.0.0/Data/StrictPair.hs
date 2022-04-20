module Data.StrictPair (strictPair) where

-- | Evaluate both argument to WHNF and create a pair of the result.
strictPair :: a -> b -> (a, b)
strictPair x y = x `seq` y `seq` (x, y)
{-# INLINE strictPair #-}
