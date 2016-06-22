
{-@ LIQUID "--higherorder"      @-}
{-@ LIQUID "--autoproofs"      @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{- LIQUID "--extensionality"  @-}
module Append where

import Prelude hiding (id)

import Proves

{- 
{-@ axiomatize id @-}
id :: a -> a
id x = x
-}
 
{-@ fmap_id :: () -> {false  } @-}
fmap_id :: () ->  Proof
fmap_id _ = fun_eq f g (\x -> simpleProof)

{-@ fun_eq :: f:(a -> b) -> g:(a -> b) 
   -> (x:a -> {f x == g x}) -> {f == g} 
  @-}   
fun_eq :: (a -> b) -> (a -> b) -> (a -> Proof) -> Proof   
fun_eq = undefined 

f :: Int -> Int 
g :: Int -> Int 
f = \r ->  r 
g = \r -> r 

{-
{-@ f :: {v:_ | v == (\r:int -> id r)} @-}
{-@ g :: {v:_ | v == (\r:int -> r)} @-}
  

-}

{- 

{-@ id_proof :: x:a -> {x == id x} @-}
id_proof :: a -> Proof 
id_proof x
  =   id x 
  ==! x 
  *** QED 

-}