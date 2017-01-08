module SplashVector where

import Prelude hiding (length)
import Data.Vector (Vector, (!), length)

vectorSum :: (Num a) => Vector a -> a
vectorSum x = sum [ x ! i | i <- [ 0 .. n ]]
  where
    n       = length x

{-@ foo :: n:Int -> [{v:Nat | v <= n}] @-}
foo :: Int -> [Int]
foo n = [0 .. n]

{-@ assume GHC.Enum.enumFromTo :: (Enum a) => lo:a -> hi:a -> [{v:a | lo <= v && v <= hi}] @-}















--------------------------------------------------------------------------------
