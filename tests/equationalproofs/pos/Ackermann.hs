{-
Proving ackermann properties from http://www.cs.yorku.ca/~gt/papers/Ackermann-function.pdf
-}


{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE FlexibleContexts     #-}
{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--autoproofs"      @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--no-prune"        @-}
{-@ LIQUID "--maxparams=5"     @-}


module FunctionAbstraction where
import Axiomatize
import Equational 




{-
TODO
  - allow terminating expressions for assumed
  - allow preconditions in assumed 
  - provide assumed types for ack with axiomatization
-}

{-@ measure ack :: Int -> Int -> Int @-}
-- assumed specs cannot have termination expressions 


{-@ assume ack :: n:Nat -> x:Nat
      -> {v:Nat| v == ack n x && if n == 0 then v == x + 2 else (if x == 0 then v == 2 else v == (ack (n-1) (ack n (x-1))))}@-}

{-@ ack :: n:Nat -> x:Nat -> Nat / [n, x] @-}
ack :: Int -> Int -> Int 
ack n x 
  | n == 0
  = x + 2
  | x == 0 
  = 2 
  | n > 0, x > 0 
  = ack (n-1) (ack n (x-1))


{-@ Lazy iack @-}
{-@ measure iack :: Int -> Int -> Int -> Int @-}
{-@ iack :: Nat -> Nat -> Nat -> Int @-}
{-@ assume iack :: h:Nat -> n:Nat -> x:Nat 
                -> {v:Nat | v == iack h n x && if h == 0 then (v == ack n x) else (v == ack n (iack (h-1) n x) )} @-}
iack :: Int -> Int -> Int -> Int 
iack h n x = if h == 0 then ack n x else ack n (iack (h-1) n x)


-- Lemma 2.2

lemma2 :: Int -> Int -> Bool 
{-@ lemma2 :: n:Nat -> x:Nat -> {v:Bool | x + 1 < ack n x } / [n, x] @-}
lemma2 n x 
  | x == 0 
  = ack n 0 == 2
  | n == 0 
  = ack 0 x == x + 1  
  | otherwise
  = ack n x  == ack (n-1) (ack n (x-1)) `with` 
    lemma2 (n-1) (ack n (x-1))          `with`
    (ack n (x-1)) + 1 < ack n x         `with`
    lemma2 n (x-1)                      `with`
    x < ack n (x-1)   

-- Lemma 2.3 
lemma3 :: Int -> Int -> Bool 
{-@ lemma3 :: n:Nat -> x:Nat -> {v:Bool | ack n x < ack n (x+1)} @-}
lemma3 n x 
  | x == 0 
  = ack n 0 < ack n 1 `with` 
    ack n 0 == 2      `with` 
    lemma2 n 1        `with`
    2 < ack n 1 
  | n == 0 
  = ack n x < ack n (x + 1)
  | otherwise
  = ack n (x+1)  == ack (n-1) (ack n x) `with`
    lemma2 (n-1) (ack n x)              `with`
    ack n x < ack n (x+1) 


lemma3' :: Int -> Int -> Int -> Bool 
{-@ lemma3' :: n:Nat -> x:Nat -> y:{v:Nat | x < v} -> {v:Bool | ack n x < ack n y} / [y] @-}
lemma3' n x y 
  | x + 1 < y 
  = lemma3' n x (y-1)      `proves`
     ack n x < ack n (y-1)  `with` 
     lemma3 n (y-1)        `proves`
     ack n x < ack n y 


  | x + 1 == y 
  = lemma3 n x `with` 
     ack n x < ack n y 
     
  | otherwise
  = True


lemma3'' :: Int -> Int -> Int -> Bool 
{-@ lemma3'' :: n:Nat -> x:Nat -> y:{v:Nat | x <= v} -> {v:Bool | ack n x <= ack n y} / [y] @-}
lemma3'' n x y 
  | x == y 
  = ack n x == ack n y 
  | otherwise
  = lemma3' n x y 


-- Lemma 2.4 

lemma4 :: Int -> Int -> Bool 
{-@ lemma4 :: n:Nat -> x:{Int | x > 0 } -> {v:Bool | ack n x < ack (n+1) x } @-}
lemma4 n x
  = lemma2 (n+1) (x-1) `proves` 
      x < ack (n+1) (x-1) `with`
    lemma3' n x (ack (n+1) (x-1)) `proves`
      ack n x < ack n (ack (n+1) (x-1)) `with`
      ack (n+1) x == ack n (ack (n+1) (x-1)) `with`
      ack n x < ack (n+1) x 


lemma4' :: Int -> Int -> Bool 
{-@ lemma4' :: n:Nat -> x:Nat -> {v:Bool | ack n x <= ack (n+1) x } @-}
lemma4' n x
  | x == 0 
  = ack n x     == 2 `with`
    ack (n+1) x == 2  
  | otherwise
  = lemma4 n x 


-- Lemma 2.5 

lemma5 :: Int -> Int -> Int -> Bool 
{-@ lemma5 :: h:Nat -> n:Nat -> x:Nat
           -> {v:Bool | iack h n x < iack (h+1) n x } @-}
lemma5 h n x
  = lemma2 n (iack h n x) `proves`
    iack h n x < ack n (iack h n x) `with`
    iack (h+1) n x == ack n (iack h n x)


-- Lemma 2.6 
lemma6 :: Int -> Int -> Int -> Bool 
{-@ lemma6 :: h:Nat -> n:Nat -> x:Nat
           -> {v:Bool | iack h n x < iack h n (x+1) } @-}

lemma6 h n x
   | h == 0 
   = 
    iack 0 n x     == ack n x `with` 
    iack 0 n (x+1) == ack n (x+1) `with`
    ack n x < ack n (x+1) `with` 
    lemma3 n x `with`
    iack h n x < iack h n (x+1) 
  | h > 0 
  = lemma6 (h-1) n x `with` 
    iack (h-1) n x < iack (h-1) n (x+1) `with` 
    lemma3' n (iack (h-1) n x) (iack (h-1) n (x+1)) `with`
    ack n (iack (h-1) n x) < ack n (iack (h-1) n (x+1)) `with`
    ack n (iack (h-1) n x) == iack h n x `with`
    ack n (iack (h-1) n (x+1)) == iack h n (x+1) `with`
    iack h n x < iack h n (x+1) `with` 
    iack h n x < iack h n (x+1)

lemma7 :: Int -> Int -> Int -> Bool 
{-@ lemma7 :: h:Nat -> n:Nat -> x:Nat
           -> {v:Bool | iack h n x <= iack h (n+1) x } @-}
lemma7 h n x 
  | x == 0 , h == 0 
  = iack 0 n 0 == ack n 0 `with` 
    ack n 0 == 2 `with`
    iack 0 (n+1) 0 == ack (n+1) 0 `with` 
    ack (n+2) 0 == 2 

  | h == 0
  = iack 0 n x == ack n x `with` 
    iack 0 (n+1) x == ack (n+1) x `with` 
    lemma4 n x 

  | h > 0 
  = iack h n x == ack n (iack (h-1) n x) `with` 
    lemma4' n (iack (h-1) n x) `with` 
    ack n (iack (h-1) n x) <= ack (n+1) (iack (h-1) n x) `with`
    lemma7 (h-1) n x `with`
    iack (h-1) n x <= iack (h-1) (n+1) x `with` 
    lemma3'' (n+1) (iack (h-1) n x) (iack (h-1) (n+1) x) `with` 
    ack (n+1) (iack (h-1) n x) <= ack (n+1) (iack (h-1) (n+1) x) `with`
    ack (n+1) (iack (h-1) (n+1) x) == iack h (n+1) x 


{-  desired proof 
       iack h n x 
     === ack n (iack (h-1) n x) {- lemma4: ack n x < ack (n+1) x-}
       < ack (n+1) (iack (h-1) n x) 
       {- IH iack (h-1) n c <= iack (h-1) (n+1) x -}
       {- lemma3' ack (n+1) (iack (h-1) n c) <= ack (n+1) (iack (h-1) (n+1) x) -}
       <= ack (n+1) (iack (h-1) (n+1) x)
     === iack h (n+1) x 
-}


infixr 2 `with`
infixr 2 `proves`


{-@ with, proves  :: p:Bool -> q:Bool -> {v:Bool | Prop v <=> Prop p && Prop q } @-}
proves, with :: Bool -> Bool -> Bool
with   p q = p && q 
proves p q = p && q 





