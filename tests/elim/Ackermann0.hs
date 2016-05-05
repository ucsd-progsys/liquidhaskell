
-- | Proving ackermann properties from
-- | http://www.cs.yorku.ca/~gt/papers/Ackermann-function.pdf

{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{- LIQUID "--maxparams=5"     @-}
{-@ LIQUID "--eliminate"       @-}
{- LIQUID "--scrape-internals" @-}


module Ackermann where

import Proves
-- import Helper

-- | First ackermann definition

{-@ axiomatize ack @-}
{-@ ack :: n:Nat -> x:Nat -> Nat / [n, x] @-}
ack :: Int -> Int -> Int
ack n x
  | n == 0
  = x + 2
  | x == 0
  = 2
  | otherwise
  = ack (n-1) (ack n (x-1))

-- | Second ackermann definition

{-@ axiomatize iack @-}
{-@ iack :: Nat -> Nat -> Nat -> Nat @-}
{- measure iack :: Int -> Int -> Int -> Int @-}
{- iack :: h:Nat -> n:Nat -> x:Nat -> {v:Nat | v == iack h n x && v == if h == 0 then x else ack n (iack (h-1) n x) } @-}
iack :: Int -> Int -> Int -> Int
iack h n x
  = if h == 0 then x else ack n (iack (h-1) n x)

-- | Equivalence of definitions

{-@ def_eq :: n:Nat -> x:Nat -> {v:Proof | ack (n+1) x == iack x n 2 }  / [x]@-}
def_eq :: Int -> Int -> Proof
def_eq n x
  = undefined

lemma3_eq :: Int -> Int -> Int -> Proof
{-@ lemma3_eq :: n:Nat -> x:Nat -> y:{Nat | x <= y} -> {v:Proof | ack n x <= ack n y} / [y] @-}
lemma3_eq n x y
  = undefined



-- | Lemma 2.4
{-@ type Pos = {v:Int | 0 < v } @-}

lemma4 :: Int -> Int -> Proof
{-@ lemma4 :: x:Pos -> n:Nat -> {v:Proof | ack n x < ack (n+1) x } @-}
lemma4 x n
  = undefined


lemma4_eq     :: Int -> Int -> Bool
{-@ lemma4_eq :: n:Nat -> x:Nat -> {v:Bool | ack n x <= ack (n+1) x } @-}
lemma4_eq n x
  = undefined


-- Lemma 2.7

lemma7 :: Int -> Int -> Int -> Bool
{-@ lemma7 :: h:Nat -> n:Nat -> x:Nat
           -> {v:Bool | iack h n x <= iack h (n+1) x } @-}
lemma7 h n x
  | x == 0 , h == 0
  = proof $
     iack 0 n 0 ==! (0 :: Int)
                ==! iack 0 (n+1) 0
  | h == 0
  = proof $
      iack 0 n x ==! x
                 ==! iack 0 (n+1) x
  | h > 0
  = proof $
      iack h n x ==! ack n (iack (h-1) n x)
                 <=! ack (n+1) (iack (h-1) n x)     ? lemma4_eq n (iack (h-1) n x)
                 <=! ack (n+1) (iack (h-1) (n+1) x) ? (lemma7 (h-1) n x
                                                     &&& lemma3_eq (n+1) (iack (h-1) n x) (iack (h-1) (n+1) x)
                                                      )
                 <=! iack h (n+1) x ? True
