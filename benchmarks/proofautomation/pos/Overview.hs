{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}

module FunctionAbstraction where
import Language.Haskell.Liquid.ProofCombinators
import Helper

{-@ LIQUID "--automatic-instances=liquidinstances" @-}
{- LIQUID "--proof-method=arithmetic" @-}


fib :: Int -> Int
fib n
  | n == 0    = 0
  | n == 1    = 1
  | otherwise = fib (n-1) + fib (n-2)


{-@ fib :: n:Nat -> Nat @-}
{-@ reflect fib @-}

-- | How do I teach the logic the implementation of fib?
-- | Two trends:
-- | Dafny, F*, HALO: create an SMT axiom
-- | forall n. fib n == if n == 0 then 0 else if n == 1 == 1 else fib (n-1) + fib (n-2)

-- | Problem: When does this axiom trigger?
-- | undefined: unpredicted behaviours + the butterfly effect

-- | LiquidHaskell: logic does not know about fib:
-- | reffering to fib in the logic will lead to un sorted refinements


{- unsafe :: _ -> { fib 2 == 1 } @-}
unsafe () = ()

{-@ safe :: () -> { fib 2 == 1 } @-}
safe :: () -> Proof
safe () = trivial 

-- increase fuel to instantiate 3 times!
{-@ automatic-instances safe' with 3 @-}

{-@ safe' :: () ->  { fib 3 == 2 } @-}
safe' () = trivial 


{-@ safe'' :: () ->  { fib 3 == 2 } @-}
safe'' () = safe () 


fib_incr_gen :: Int -> Int -> Proof
{-@ fib_incr_gen :: n:Nat -> m:Greater n -> {fib n <= fib m}
  @-}
fib_incr_gen
  = gen_incr fib fib_incr

fib_incr :: Int -> Proof
{-@ fib_incr :: n:Nat -> {fib n <= fib (n+1)} @-}
fib_incr n
   | n == 0
   = trivial
   | n == 1
   = trivial
   | otherwise
   = fib_incr (n-1) &&& fib_incr (n-2)
