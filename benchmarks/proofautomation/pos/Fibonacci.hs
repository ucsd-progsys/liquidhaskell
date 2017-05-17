{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
{-@ LIQUID "--proof-method=arithmetic" @-}


module Fibonacci where
import Language.Haskell.Liquid.ProofCombinators


-- | Proves that the fibonacci function is increasing


-- | Definition of the function in Haskell
-- | the annotation axiomatize means that
-- | in the logic, the body of increase is known
-- | (each time the function fib is applied,
-- | there is an unfold in the logic)

{-@ fib :: n:Nat -> Nat @-}

{-@ reflect fib @-}

fib :: Int -> Int
fib n
  | n == 0    = 0
  | n == 1    = 1
  | otherwise = fib (n-1) + fib (n-2)

-- | How to encode proofs:
-- | ==., <=., and <. stand for the logical ==, <=, < resp.
-- | If the proofs do not derive automatically, user can
-- | optionally provide the Proofean statements, after `?`
-- | Note, no inference occurs: logic only reasons about
-- | linear arithmetic and equalities

lemma_fib :: Int -> Proof
{-@ lemma_fib :: x:{Nat | 1 < x } -> { 0 < fib x } @-}
lemma_fib x
  | x == 2
  = ((fib 1)*** QED)
  | 2 < x
  = lemma_fib (x-1) &&& ((fib x, fib (x-1), fib (x-2)) *** QED)


{-@ fib_increasing :: x:Nat -> y:{Nat | x < y} -> { fib x <= fib y } / [x, y] @-}
fib_increasing :: Int -> Int -> Proof
fib_increasing x y
  | x == 0, y == 1
  = trivial
  | x == 0
  = lemma_fib y
  | x == 1, y == 2
  = trivial
  | x == 1, 2 < y
  = fib_increasing 1 (y-1)
  | otherwise
  = fib_increasing (x-2) (y-2) &&& fib_increasing (x-1) (y-1)
