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
{-@ Lazy ack @-}
{-@ assume 
  ack :: n:Nat -> x:Nat
      -> {v:Nat| v == ack n x && if n == 0 then v == x + 2 else (if x == 0 then v == 2 else v == (ack (n-1) (ack n (x-1))))}@-}
ack :: Int -> Int -> Int 
ack n x 
  | n == 0
  = x + 2
  | x == 0 
  = 2 
  | n > 0, x > 0 
  = ack (n-1) (ack n (x-1))
  -- this cannot be proven, because assumed types ignore precondition specs 
  | otherwise
  = 0 

-- Lemma 2.2

prop_ack_1 :: Int -> Int -> Bool 
{-@ prop_ack_1 :: n:Nat -> x:Nat -> {v:Bool | x + 1 < ack n x } / [n, x]@-}
prop_ack_1 n x 
  | x == 0 
  = ack n 0 == 2
  | n == 0 
  = ack 0 x == x + 1  
  | otherwise
  = ack n x  == ack (n-1) (ack n (x-1)) `with` 
    prop_ack_1 (n-1) (ack n (x-1)) `with`
    (ack n (x-1)) + 1 < ack n x `with`
    prop_ack_1 n (x-1) `with`
    x < ack n (x-1)   




infixr 2 `with`

{-@ with :: forall <p :: Bool -> Prop, q::Bool -> Prop, r :: Bool -> Prop>. 
                 {vp::Bool<p> |- Bool<q> <: Bool<r> }
                 Bool<p> -> Bool<q> -> Bool<r> @-}

with :: Bool -> Bool -> Bool
with _ r = r