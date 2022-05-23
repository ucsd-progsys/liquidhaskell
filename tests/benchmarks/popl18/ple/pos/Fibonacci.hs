{-@ LIQUID "--higherorder"     @-}	
{-@ LIQUID "--ple" @-}

-- TAG: absref

module Fibonacci where
import Language.Haskell.Liquid.ProofCombinators


-- | Proves that the fibonacci function is increasing


-- | Definition of the function in Haskell
-- | the annotation axiomatize means that
-- | in the logic, the body of increase is known
-- | (each time the function fib is applied,
-- | there is an unfold in the logic)

{-@ reflect fib @-}

fib :: Int -> Int
{-@ fib :: i:Nat -> Nat @-}
fib i | i == 0    = 0
      | i == 1    = 1
      | otherwise = fib (i-1) + fib (i-2)

{-@ fib1 :: () -> {fib 16 == 987 } @-}
fib1 :: () -> Proof
fib1 _ = trivial

fibUp :: Int -> Proof
{-@ fibUp :: i:Nat -> {fib i <= fib (i+1)} @-}
fibUp i
  | i == 0
  =   [fib 0, fib 1] *** QED
  | i == 1
  =  [fib 1, fib 0, fib 2] *** QED
  | otherwise
  = [[fib (i+1), fib i] *** QED , fibUp (i-1), fibUp (i-2)] *** QED
{-
  | otherwise
  =   fibUp (i-1)
  &&& fibUp (i-2)
-}

-- 0, 1, 2, 3, 4, 5, 6, 7,   8,  9, 10, 11,  12, 13,   14,  15, 16
-- 0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987


{-
FStar failing

val fib: x:int{x>=0} -> Tot int
let rec fib n =
  if n = 0 then 0
  else if n = 1 then 1 else fib (n-1) + fib (n-2)


val prop: x:int -> Tot (v:int {fib 15 = 610})
let prop x =  0

-}

-- | How to encode proofs:
-- | ==., <=., and <. stand for the logical ==, <=, < resp.
-- | If the proofs do not derive automatically, user can
-- | optionally provide the Proofean statements, after `?`
-- | Note, no inference occurs: logic only reasons about

{-
fibUp :: Int -> Proof
{-@ fibUp :: i:Nat -> {fib i <= fib (i+1)} @-}
fibUp i
  | i == 0
  =   trivial
  | i == 1
  =  trivial --  fib 2 *** QED
  | otherwise
  =   fibUp (i-1)
  &&& fibUp (i-2)
-}
{-
Explicit Proof
fibMonotonic x y
  | y == x + 1
  =   fib x
  <=. fib (x+1) ? fibUp x
  <=. fib y
  *** QED
  | x < y - 1
  =   fib x
  <=. fib (y-1) ? fibMonotonic x (y-1)
  <=. fib y     ? fibUp (y-1)
  *** QED

FStar Proof

val fibUp :i:int{0 <= i} -> Tot (v:int {fib i <= fib (i+1)})
let rec fibUp i =
    if i=0 then 0 else
    if i=1 then 1 else (fibUp (i-1) + fibUp (i-2))
-}


fibMonotonic :: Int -> Int -> Proof
{-@ fibMonotonic :: x:Nat -> y:{Nat | x < y }
     -> {fib x <= fib y}  / [y] @-}
fibMonotonic x y
  | y == x + 1
  =   fibUp x
  | x < y - 1
  =   fibMonotonic x (y-1)
  &&& fibUp (y-1)


fMono :: (Int -> Int)
      -> (Int -> Proof)
      -> Int -> Int -> Proof
{-@ fMono :: f:(Nat -> Int)
          -> fUp:(z:Nat -> {f z <= f (z+1)})
          -> x:Nat
          -> y:{Nat|x < y}
          -> {f x <= f y} / [y] @-}
fMono f fUp x y
  | x + 1 == y
  = fUp x
  | x + 1 < y
  =   fMono f fUp x (y-1)
  &&& fUp (y-1)


fibMonoHO :: Int -> Int -> Proof
{-@ fibMonoHO :: n:Nat -> m:{Nat | n < m }  -> {fib n <= fib m} @-}
fibMonoHO     = fMono fib fibUp

-- forall n:Nat. exists m: (n<m => exists m'. fib n <== m')
fibEx :: Int -> (Int, Proof) -> (Int, Proof)
{-@ fibEx :: n:Nat -> (m::Int, {v:Proof | n < m})
         -> (m'::Int, {v:Proof | fib n <= m' }) @-}
fibEx n (m, pf) = (fib m, fibMonoHO n m)
