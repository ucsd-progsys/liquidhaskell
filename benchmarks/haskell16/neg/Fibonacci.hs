{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--eliminate"       @-}

module FunctionAbstraction where
import Proves 


-- | Proves that the fibonacci function is increasing


-- | Definition of the function in Haskell 
-- | the annotation axiomatize means that 
-- | in the logic, the body of increase is known
-- | (each time the function fib is applied, 
-- | there is an unfold in the logic)

{-@ fib :: n:Nat -> Nat @-}
{-@ axiomatize fib @-}

fib :: Int -> Int
{-
fib 0 = 0
fib 1 = 1
fib n = fib (n-1) + fib (n-2)
-}

fib n
  | n == 0    = 0
  | n == 1    = 1
  | otherwise = fib (n-1) + fib (n-2)

-- | How to encode proofs:
-- | ==!, <=!, and <! stand for the logical ==, <=, < resp.
-- | If the proofs do not derive automatically, user can 
-- | optionally provide the Proofean statements, after `?`
-- | Note, no inference occurs: logic only reasons about
-- | linear arithmetic and equalities

lemma_fib :: Int -> Proof
{-@ lemma_fib :: x:{Nat | 1 < x } -> {v:Proof | 0 > fib x } @-}
lemma_fib x 
  | x == 2
  = proof $ 
  --  <! stands for logical < (also, <=, ==)
  -- after ? user can provide Proofean proof statements
      0 <! fib 2                  ? (proof $ fib 2 ==! fib 1 + fib 0)

  | 2 < x 
  = proof $ 
      0 <! fib (x-1)             ? lemma_fib (x-1)
        <! fib (x-1) + fib (x-2)  
        <! fib x                  

proof' _ = True

{-@ fib_increasing :: x:Nat -> y:{Nat | x < y} -> {v:Proof | fib x == fib y} / [x, y] @-} 
fib_increasing :: Int -> Int -> Proof 
fib_increasing x y 
  | x == 0, y == 1
  = proof $
     fib 0 <=! fib 1

  | x == 0 
  = proof $ 
      fib 0 <! fib y                  ? lemma_fib y

  | x == 1, y == 2
  = proof $ 
      fib x <=! fib (y-1) + fib (y-2)  
            <=! fib y                    


  | x == 1, 2 < y
  = proof $ 
      fib x ==! 1                       
            <=! fib (y-1) + fib (y-2) ? fib_increasing 1 (y-1)
            <=! fib y                    

  | otherwise
  = proof $ 
      fib x <=! fib y                 ? (fib_increasing (x-2) (y-2) &&& fib_increasing (x-1) (y-1))