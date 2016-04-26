{-
Proving ackermann properties from http://www.cs.yorku.ca/~gt/papers/Ackermann-function.pdf
-}


{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE FlexibleContexts     #-}
{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--autoproofs"      @-}
{- LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--no-prune"        @-}


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


-- Lemma 2.5 

lemma5 :: Int -> Int -> Int -> Bool 
{-@ lemma5 :: h:Nat -> n:Nat -> x:Nat
           -> {v:Bool | iack h n x < iack (h+1) n x } @-}
lemma5 h n x
  = lemma2 n (iack h n x) `proves`
    iack h n x < ack n (iack h n x) `with`
    iack (h+1) n x == ack n (iack h n x)

infixr 2 `with`
infixr 2 `proves`

{-@ proves, with :: forall <p :: Bool -> Prop, q::Bool -> Prop, r :: Bool -> Prop>. 
                     {vp::Bool<p> |- Bool<q> <: Bool<r> }
                     Bool<p> -> Bool<q> -> Bool<r> @-}

proves, with :: Bool -> Bool -> Bool
with   _ r = r
proves _ r = r



