{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}

{-@ LIQUID "--instantiate=liquidinstances" @-}

{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE FlexibleContexts    #-}


module MapFusion where

import Prelude hiding (map)

import Language.Haskell.Liquid.ProofCombinators

{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

{-@ axiomatize map @-}
map :: (a -> b) -> L a -> L b
map f N = N 
map f (C x xs) = C (f x) (map f xs)
 


{-@ map_fusion :: f:(a -> a) -> g:(a -> a) -> xs:{L a | true }
   -> {map (compose f g) xs == compose (map f) (map g) xs } @-}
map_fusion :: (a -> a) -> (a -> a) -> L a -> Proof
map_fusion f g N        = trivial 
map_fusion f g (C x xs) = map_fusion f g xs 


data L a = N | C a (L a)
{-@ data L [llen] a = N | C {headlist :: a, taillist :: L a }@-}

{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen N        = 0
llen (C _ xs) = 1 + llen xs
