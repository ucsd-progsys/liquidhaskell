{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Euclide where

import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (mod, gcd)

{-@ reflect gcd @-}
{-@ gcd :: a:Nat -> b:{Nat | b < a } -> Int @-}
gcd :: Int -> Int -> Int 
gcd a b 
  | b == 0 || a == 0 
  = a 
  | otherwise 
  = gcd b (a `modr` b)

{-@ reflect modr @-}
{-@ modr :: a:Nat -> b:{Int | 0 < b} -> {v:Nat | v < b } @-}
modr :: Int -> Int -> Int 
modr a b 
  | a < b = a 
  | otherwise 
  = modr (a-b) b

