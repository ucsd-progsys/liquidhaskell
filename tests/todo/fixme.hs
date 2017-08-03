{-@ LIQUID "--higherorder"     @-}
{- LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{- LIQUID "--higherorderqs" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}


{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts      #-}

module Append where

import Prelude hiding (map, concatMap)

import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize append @-}
append :: L a -> L a -> L a
append Emp      ys = ys
append (x:::xs) ys = x ::: append xs ys

{-@ axiomatize map @-}
map :: (a -> b) -> L a -> L b
map f Emp        = Emp
map f (x ::: xs) = f x ::: map f xs 

{-@ axiomatize concatMap @-}
concatMap :: (a -> L b) -> L a -> L b
concatMap f Emp        = Emp 
concatMap f (x ::: xs) = append (f x) (concatMap f xs)

{-@ axiomatize concatt @-}
concatt :: L (L a) -> L a
concatt Emp      = Emp
concatt (x:::xs) = append x (concatt xs)

{-@ prop_concatMap :: f:(a -> L (L a)) -> xs:L a
                   -> { concatt (map f xs) == concatMap f xs }
  @-}

prop_concatMap :: (a -> L (L a)) -> L a -> Proof
prop_concatMap _ Emp        = trivial
prop_concatMap f (x ::: xs) = prop_concatMap f xs


data L a = Emp | a ::: L a
{-@ data L [llen] a = Emp | (:::) {x::a, xs :: L a } @-}


{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen Emp        = 0
llen (_ ::: xs) = 1 + llen xs

