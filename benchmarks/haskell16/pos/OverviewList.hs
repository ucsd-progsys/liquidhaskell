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


fib_incr_gen :: Int -> Int -> Proof
{-@ fib_incr_gen :: n:Nat -> m:Greater n -> {fib n <= fib m}
  @-}
fib_incr_gen
  = gen_incr fib fib_incr

fib_incr :: Int -> Proof
{-@ fib_incr :: n:Nat -> {fib n <= fib (n+1)} @-}
fib_incr n
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
              ? fib_incr (n-1)
          <=! fib n     + fib (n-1)
              ? fib_incr (n-2)
          <=! fib (n+1)
