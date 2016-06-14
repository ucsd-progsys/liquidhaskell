
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


{-@ measure fib :: Int -> Int @-}
{-@ assume fib ::
         n:Nat 
      -> {v:Nat| v == fib n && if n == 0 then v == 0 else (if n == 1 then v == 1 else v == fib (n-1) + fib (n-2)) } @-}
fib :: Int -> Int 
fib n 
  | n <  0    = error "cannot happen" 
  | n == 0    = 0 
  | n == 1    = 1
  | otherwise = fib (n-1) + fib (n-2)

infixr 2 `with`

{-@ with :: forall <p :: Bool -> Prop, q::Bool -> Prop, r :: Bool -> Prop>. 
                 {vp::Bool<p> |- Bool<q> <: Bool<r> }
                 Bool<p> -> Bool<q> -> Bool<r> @-}

with :: Bool -> Bool -> Bool
with _ r = r

fib_increasing0 :: Int -> Bool
{-@ fib_increasing0 :: x:{Nat | x > 1} -> {v:Bool | fib x > 0} @-}
fib_increasing0 x 
  | x == 2
  = fib 2 == fib 1 + fib 0 `with` fib x > 0 
  | x > 2 
  = fib_increasing0 (x-1) `with` 
    fib (x-2) >= 0        `with` 
    fib x > 0

{-@ fib_increasing :: x:Nat -> y:{Nat | x < y} -> {v:Bool | fib x < fib y} / [x, y] @-} 
fib_increasing :: Int -> Int -> Bool 
fib_increasing x y 
  | x == 0, y == 1
  = fib y == 1 `with` fib x == 0
  | x == 0
  = fib_increasing0 y `with` fib x == 0 
  | x == 1, y == 2
  = fib x == 1 `with`
    fib y == fib (y-1) + fib (y-2) 
  | x == 1, 2 < y
  = fib x == 1 `with` fib y == fib (y-1) + fib (y-2) `with`
    2 < y `with` fib_increasing 1 (y-1) `with`
    1 < fib (y-1) `with` 0 < fib (y-2) 
  | otherwise
  = fib x == fib (x-1) + fib (x-2) `with`
    fib y == fib (y-1) + fib (y-2) `with`
    fib_increasing (x-1) (y-1) `with`
    fib (x-1) <= fib (y-1) `with` 
    fib_increasing (x-2) (y-2) `with`
    fib (x-2) <= fib (y-2) 
