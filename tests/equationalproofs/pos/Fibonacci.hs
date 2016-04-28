{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}

module FunctionAbstraction where

import Proves 

{-@ measure fib :: Int -> Int @-}
{-@ fib :: n:Nat -> Nat @-}
{-@ assume fib ::
         n:Nat 
      -> {v:Nat| v == fib n && if n == 0 then v == 0 else (if n == 1 then v == 1 else v == fib (n-1) + fib (n-2)) } @-}
fib :: Int -> Int 
fib n 
  | n == 0    = 0 
  | n == 1    = 1
  | otherwise = fib (n-1) + fib (n-2)


lemma_fib :: Int -> Bool
{-@ lemma_fib :: x:{Nat | 1 < x } -> {v:Bool | 0 < fib x } @-}
lemma_fib x 
  | x == 2
  = proof $ 
      0 <: fib 2                 ? (fib 2 == fib 1 + fib 0)

  | 2 < x 
  = proof $ 
      0 <:  fib (x-1)            ? lemma_fib (x-1)
        <: fib (x-1) + fib (x-2) ? True 
        <: fib x                 ? True 



{-@ fib_increasing :: x:Nat -> y:{Nat | x < y} -> {v:Bool | fib x <= fib y} / [x, y] @-} 
fib_increasing :: Int -> Int -> Bool 
fib_increasing x y 
  | x == 0, y == 1
  = proof $
     fib 0 <=: fib 1                  ? True

  | x == 0 
  = proof $ 
      fib 0 <: fib y                  ? lemma_fib y

  | x == 1, y == 2
  = proof $ 
      fib x <=: fib (y-1) + fib (y-2) ? True 
            <=: fib y                 ? True   


  | x == 1, 2 < y
  = proof $ 
      fib x ==: 1                     ? True 
            <=: fib (y-1) + fib (y-2) ? fib_increasing 1 (y-1)
            <=: fib y                 ? True   

  | otherwise
  = proof $ 
      fib x <=: fib y                 ? (fib_increasing (x-2) (y-2) && fib_increasing (x-1) (y-1))
