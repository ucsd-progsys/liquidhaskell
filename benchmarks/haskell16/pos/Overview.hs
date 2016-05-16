{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--eliminate"       @-}

module FunctionAbstraction where
import Proves
import Helper

{-@ fib :: n:Nat -> Nat @-}
{-@ axiomatize fib @-}

fib :: Int -> Int
fib n
  | n == 0    = 0
  | n == 1    = 1
  | otherwise = fib (n-1) + fib (n-2)


fib_increasing_gen :: Int -> Int -> Proof
{-@ fib_increasing_gen :: n:Nat -> m:{Nat | n < m } -> {fib n <= fib m} 
  @-}
fib_increasing_gen
  = gen_increasing_eq fib fib_increasing

fib_increasing :: Int -> Proof
{-@ fib_increasing :: n:Nat -> {fib n <= fib (n+1)} @-}
fib_increasing n
   | n == 0
   = proof $
      fib 0 <! fib 1
   | n == 1
   = proof $
      fib 1 <=! fib 1 + fib 0
            <=! fib 2
   | otherwise
   = proof $
       fib n
          ==! fib (n-1) + fib (n-2)
          <=! fib n     + fib (n-2)
              ? fib_increasing (n-1)
          <=! fib n     + fib (n-1)
              ? fib_increasing (n-2)
          <=! fib (n+1)
