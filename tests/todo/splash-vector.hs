{-# LANGUAGE OverloadedStrings #-}
module SplashVector where

import Prelude hiding (length)
-- import Data.Vector (Vector, (!), length)
import qualified Data.Vector            as V
import qualified Data.ByteString        as B
import qualified Data.ByteString.Unsafe as B

-- REPLACE `n` with `n - 1`

vectorSum :: (Num a) => V.Vector a -> a
vectorSum x = sum [ x V.! i | i <- [ 0 .. n ]]
  where
    n       = V.length x

-- REPLACE 60 with 6
liquid :: B.ByteString
liquid = B.unsafeTake 60 (pack "LiquidHaskell")



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
