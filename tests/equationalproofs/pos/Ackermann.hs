
-- | Proving ackermann properties from
-- | http://www.cs.yorku.ca/~gt/papers/Ackermann-function.pdf

{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--autoproofs"      @-}
{-@ LIQUID "--totality"        @-}
{- LIQUID "--maxparams=5"     @-}


module FunctionAbstraction where

import Proves

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

{-@ def_eq :: n:Nat -> x:Nat -> {v:Proof | ack (n+1) x == iack x n 2 }  / [x]@-}
def_eq n x
  | x == 0
  = proof $
     ack (n+1) 0 ==! 2
                 ==! iack 0 n 2

  | otherwise
  = proof $
      ack (n+1) x ==! ack n (ack (n+1) (x-1))
                  ==! ack n (iack (x-1) n 2 ) ? def_eq n (x-1)
                  ==! iack x n 2
