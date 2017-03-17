{-# LANGUAGE OverloadedStrings #-}
module SplashVector where

import Prelude hiding (length)
import Data.Vector (Vector, (!), length)
-- import qualified Data.Vector            as V
import qualified Data.ByteString        as B
import qualified Data.ByteString.Unsafe as B

vectorSum :: (Num a) => Vector a -> a
dotProduct :: (Num a) => Vector a -> Vector a -> a

-- vectorSum  :: `[0 .. n] ` with `[0 .. n - 1]`
-- dotProduct :: (Num a) => x:Vector a -> {y:Vector a | vlen y = vlen x} -> a
-- type VectorN a N = {v:Vector a | vlen v == N}
-- dotProduct :: (Num a) => x:Vector a -> VectorN a {vlen x} -> a



{-@ vectorSum :: (Num a) => Vector a -> a @-}
vectorSum x = sum [ x ! i | i <- [ 0 .. n - 1 ]]
  where
    n       = length x


{-@ type VectorN a N = {v:Vector a | vlen v == N} @-}

{- type VectorX a X = {v:Vector a | vlen v == vlen X} -}

{-@ type VectorEq a X = {v:Vector a | vlen v == vlen X} @-}

{-@ dotProduct :: (Num a) => x:Vector a -> VectorEq a x -> a @-}
dotProduct x y = sum [ (x ! i) * (y ! i) | i <- [0 .. n - 1]]
  where
    n          = length x






-- 60
-- 6
-- 16
-- 14


liquid :: B.ByteString
liquid = B.unsafeTake 14 (pack "LiquidHaskell  ")



{-@ assume pack :: s:String -> {v:B.ByteString | bslen v == len s} @-}
pack :: String -> B.ByteString
pack = undefined

{-@ foo :: n:Int -> [{v:Nat | v <= n}] @-}
foo :: Int -> [Int]
foo n = [0 .. n]

{-@ assume GHC.Enum.enumFromTo :: (Enum a) => lo:a -> hi:a -> [{v:a | lo <= v && v <= hi}] @-}

{-@ assume B.unsafeTake
    :: n : Nat
    -> { i : B.ByteString | n <= bslen i }
    -> { o : B.ByteString | bslen o == n }
  @-}













--------------------------------------------------------------------------------
