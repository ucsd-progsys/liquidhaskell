
-- | Proving ackermann properties from
-- | http://www.cs.yorku.ca/~gt/papers/Ackermann-function.pdf

{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--autoproofs"      @-}
{-@ LIQUID "--totality"        @-}
{- LIQUID "--maxparams=5"     @-}


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

{-
-- | Equivalence of definitions

{- def_eq :: n:Nat -> x:Nat -> {v:Proof | ack (n+1) x == iack x n 2 }  / [x]@-}
def_eq n x
  | x == 0
  = proof $
     ack (n+1) 0 ==! 2
                 ==! iack 0 n 2

  | otherwise
  = proof $
      ack (n+1) x ==! ack n (ack (n+1) (x-1))
                  ==! ack n (iack (x-1) n 2 )   ? def_eq n (x-1)
                  ==! iack x n 2


-- | Lemma 2.2

lemma2 :: Int -> Int -> Bool
{- lemma2 :: n:Nat -> x:Nat -> {v:Bool | x + 1 < ack n x } / [n, x] @-}
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
lemma3 :: Int -> Int -> Bool
{- lemma3 :: n:Nat -> x:Nat -> {v:Bool | ack n x < ack n (x+1)} @-}
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

-}

{-@ bar :: n:Int -> x:Int -> f:{(Int -> Int) | f == ack n} -> {v:Proof | f x == ack n x  } @-}
bar :: Int -> Int -> (Int -> Int ) -> Proof
bar _ _ _ = True

{-
lemma3_gen :: Int -> Int -> Int -> Bool
{- lemma3_gen :: n:Nat -> x:Nat -> y:{v:Nat | x < v} -> {v:Bool | ack n x < ack n y} / [y] @-}
lemma3_gen n x y
  = gen_increasing (ack n) (lemma3 n) x y
-}
