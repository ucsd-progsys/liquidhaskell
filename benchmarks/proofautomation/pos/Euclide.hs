{-@ LIQUID "--higherorder"      @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Euclide where

import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (mod, gcd)

{-@ axiomatize gcd @-}
{-@ gcd :: a:Nat -> b:{Nat | b < a } -> Int @-}
gcd :: Int -> Int -> Int 
gcd a b 
  | b == 0 || a == 0 
  = a 
  | otherwise 
  = gcd b (a `modr` b)

{-@ axiomatize modr @-}
{-@ modr :: a:Nat -> b:{Int | 0 < b} -> {v:Nat | v < b } @-}
modr :: Int -> Int -> Int 
modr a b 
  | a < b = a 
  | otherwise 
  = modr (a-b) b

