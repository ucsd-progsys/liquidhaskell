{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Term where

import Data.Vector.Algorithms.Common (shiftRI)
import Language.Haskell.Liquid.Prelude (choose)


{-@ loop :: twit:Nat -> l:Nat -> u:{v:Nat | v = l + twit} -> Int @-}
loop :: Int -> Int -> Int -> Int
loop twit l u 
   | u <= l    = l
   | otherwise = case compare (choose 0) 0 of
                   LT -> loop (u - (k + 1)) (k+1) u 
                   EQ -> k
                   GT -> loop (k - l) l     k 
  where k = (u + l) `shiftRI` 1

{-@ loop1 :: l:Nat -> u:{v:Nat | l <= v} -> Int / [u + l] @-}
loop1 :: Int -> Int -> Int
loop1 l u 
   | u <= l    = l
   | otherwise = case compare (choose 0) 0 of
                   LT -> loop1 (k+1) u 
                   EQ -> k
                   GT -> loop1 l     k 
  where k = (u + l) `shiftRI` 1

