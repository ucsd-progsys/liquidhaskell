
-- | Proving ackermann properties from
-- | http://www.cs.yorku.ca/~gt/papers/Ackermann-function.pdf

{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--autoproofs"      @-}
{-@ LIQUID "--totality"        @-}
{- LIQUID "--maxparams=5"     @-}
{-@ LIQUID "--eliminate"       @-}


module Ackermann where

import Proves
import Helper

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

iack :: Int -> Int -> Int -> Int
iack h n x
  = if h == 0 then x else ack n (iack (h-1) n x)

-- | Equivalence of definitions

{-@ def_eq :: n:Nat -> x:Nat -> {v:Proof | ack (n+1) x == iack x n 2 }  / [x] @-}
def_eq n x
  | x == 0
  = proof $
     ack (n+1) 0 ==! 2
                 ==! iack 0 n 2

  | otherwise
  = proof $
      ack (n+1) x ==! ack n (ack (n+1) (x-1))
                  ==! ack n (iack (x-1) n 2)   ? def_eq n (x-1)
                  ==! iack x n 2


-- | Lemma 2.2

lemma2 :: Int -> Int -> Proof
{-@ lemma2 :: n:Nat -> x:Nat -> {v:Proof | x + 1 < ack n x } / [n, x] @-}
lemma2 n x
  | x == 0
  = proof $
      ack n 0 ==! 2
  | n == 0
  = proof $
     ack 0 x ==! x + 2
  | otherwise
  = proof $
      ack n x ==! ack (n-1) (ack n (x-1))
               >! ack n (x-1)              ? lemma2 (n-1) (ack n (x-1))
               >! x                        ? lemma2 n (x-1)


-- | Lemma 2.3

-- Lemma 2.3
lemma3 :: Int -> Int -> Proof
{-@ lemma3 :: n:Nat -> x:Nat -> {v:Proof | ack n x < ack n (x+1)} @-}
lemma3 n x
  | x == 0
  = proof $
     ack n 0 <! ack n 1 ? lemma2 n 1
  | n == 0
  = proof $
    ack n x <! ack n (x + 1)
  | otherwise
  = proof $
      ack n x  <! ack (n-1) (ack n x) ? lemma2 (n-1) (ack n x)
               <! ack n (x+1)

lemma3_gen :: Int -> Int -> Int -> Proof
{-@ lemma3_gen :: n:Nat -> x:Nat -> y:{Nat | x < y} -> {v:Proof | ack n x < ack n y} / [y] @-}
lemma3_gen n x y
    = gen_increasing (ack n) (lemma3 n) x y

lemma3_eq :: Int -> Int -> Int -> Proof
{-@ lemma3_eq :: n:Nat -> x:Nat -> y:{Nat | x <= y} -> {v:Proof | ack n x <= ack n y} / [y] @-}
lemma3_eq n x y
  | x == y
  = ack n x == ack n y

  | otherwise
  = lemma3_gen n x y


-- | Lemma 2.4
{-@ type Pos = {v:Int | 0 < v } @-}

lemma4 :: Int -> Int -> Proof
{-@ lemma4 :: x:Pos -> n:Nat -> {v:Proof | ack n x < ack (n+1) x } @-}
lemma4 x n
  = proof $
      ack (n+1) x ==! ack n (ack (n+1) (x-1))
                   >! ack n x                   ?  lemma2 (n+1) (x-1)
                                               &&& lemma3_gen n x (ack (n+1) (x-1))

lemma4_gen     :: Int -> Int -> Int -> Bool
{-@ lemma4_gen :: n:Nat -> m:{Nat | n < m }-> x:Pos -> {v:Bool | ack n x < ack m x } @-}
lemma4_gen n m x
  = gen_increasing2 ack lemma4 x n m


lemma4_eq     :: Int -> Int -> Bool
{-@ lemma4_eq :: n:Nat -> x:Nat -> {v:Bool | ack n x <= ack (n+1) x } @-}
lemma4_eq n x
  | x == 0
  = proof $
      ack n x ==! ack (n+1) x
  | otherwise
  = lemma4 x n


-- | Lemma 2.5

lemma5 :: Int -> Int -> Int -> Bool
{-@ lemma5 :: h:Nat -> n:Nat -> x:Nat
           -> {v:Bool | iack h n x < iack (h+1) n x } @-}
lemma5 h n x
  = proof $
      iack h n x <! ack n (iack h n x) ? lemma2 n (iack h n x)
                 <! iack (h+1) n x


-- | Lemma 2.6
lemma6 :: Int -> Int -> Int -> Proof
{-@ lemma6 :: h:Nat -> n:Nat -> x:Nat
           -> {v:Proof | iack h n x < iack h n (x+1) } @-}

lemma6 h n x
  | h == 0
  = proof $
      iack h n x ==! x
                  <! x + 1
                  <! iack h n (x+1)
  | h > 0
  = proof (
      iack h n x ==! ack n (iack (h-1) n x) ? (  lemma6 (h-1) n x
                                             &&& lemma3_gen n (iack (h-1) n x) (iack (h-1) n (x+1))
                                              )

                  <! ack n (iack (h-1) n (x+1))
                  <! iack h n (x+1) )


lemma6_gen :: Int -> Int -> Int -> Int -> Proof
{-@ lemma6_gen :: h:Nat -> n:Nat -> x:Nat -> y:{Nat | x < y}
           -> {v:Proof | iack h n x < iack h n y } /[y] @-}
lemma6_gen h n x y
  = gen_increasing (iack h n) (lemma6 h n) x y


-- Lemma 2.7

lemma7 :: Int -> Int -> Int -> Bool
{-@ lemma7 :: h:Nat -> n:Nat -> x:Nat
           -> {v:Bool | iack h n x <= iack h (n+1) x } @-}
lemma7 h n x
  | x == 0 , h == 0
  = proof $
     iack 0 n 0 ==! iack 0 (n+2) 0

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
                 <=! iack h (n+1) x
