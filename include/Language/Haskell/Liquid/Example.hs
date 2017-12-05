{-@ LIQUID "--exactdc"     @-}
{-@ LIQUID "--higherorder" @-}

module ListExample where

import ProofCombinators
import Prelude hiding ((++))

data L a = C a (L a) | N 
{-@ data L [size] @-}

size :: L a -> Int
{-@ measure size @-}
{-@ size :: L a -> Nat @-}
size N       = 0 
size (C _ x) = 1 + size x 

{-@ reflect ++ @-}
{-@ infixr  ++ @-}
(++) :: L a -> L a -> L a 
N ++ ys        = ys 
(C x xs) ++ ys = C x (xs ++ ys)

-- Correct proofs 

{-@ leftId :: x:L a -> { x ++ N == x } @-}
leftId :: L a -> Proof 
leftId N 
  =   N ++ N 
  ==! N 
  -- the term (N ++ N ==! N) is a certificate that proves the theorem
  *** QED 

leftId (C x xs) 
  =    C x xs ++ N 
  -- proof certificate is implicit 
  ==!  C x (xs ++ N)
  -- give explicit proof certificate  
  ==? C x xs        ? leftId xs
  -- the above term is a certificate that proves the theorem
  *** QED 

{-@ leftIdWrong :: x:L a -> { x ++ N /= x } @-}
leftIdWrong :: L a -> Proof 
leftIdWrong N 
  =   N ++ N 
  ==! N 
  -- type error here
  *** QED 

leftIdWrong (C x xs) 
  =    C x xs ++ N 
  -- type error here  
  ==!  C x (N ++ N)
  -- type error here  
  ==: C x xs        
  -- this should go through because of admitted 
  *** Admitted
