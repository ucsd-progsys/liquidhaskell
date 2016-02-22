{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Term where

import Data.Vector.Algorithms.Common (shiftRI)
import Language.Haskell.Liquid.Prelude (choose)


{-@ foo :: Nat -> Int @-}
foo :: Int -> Int
foo n = go n
  where 
    go 0          = 1
    go (d :: Int) = go (d-1)


{-@ loop :: twit:Nat -> l:Nat -> u:{v:Nat | v = l + twit} -> Int @-}
loop :: Int -> Int -> Int -> Int
loop twit l u 
   | u <= l    = l
   | otherwise = case compare (choose 0) 0 of
                   LT -> loop (u - (k + 1)) (k+1) u 
                   EQ -> k
                   GT -> loop (k - l) l     k 
  where k = (u + l) `shiftRI` 1

{-@ loop1 :: l:Nat -> u:{v:Nat | l <= v} -> Int / [u - l] @-}
loop1 :: Int -> Int -> Int
loop1 l u 
   | u <= l    = l
   | otherwise = case compare (choose 0) 0 of
                   LT -> loop1 (k+1) u 
                   EQ -> k
                   GT -> loop1 l     k 
  where k = (u + l) `shiftRI` 1

{-@ loop3 :: l:Nat -> u:{v:Nat | l <= v} -> Int / [u - l] @-}
loop3 :: Int -> Int -> Int
loop3 l u
   | len < 100       = len
   | otherwise       = let a = loop3 l mid
                           b = loop3 mid u
                       in a + b
  where len = u - l
        mid = (u + l) `shiftRI` 1


