{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}

{-@ LIQUID "--automatic-instances=liquidinstances" @-}

{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE FlexibleContexts    #-}


module MapFusion where

import Prelude hiding (map)

import Language.Haskell.Liquid.ProofCombinators

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

{-@ reflect map @-}
map :: (a -> b) -> L a -> L b
map f N = N 
map f (C x xs) = C (f x) (map f xs)


{-@ map_fusion :: foo:(a -> a) -> goo:(a -> a) -> xs:{L a | true }
               -> {map (compose foo goo) xs == compose (map foo) (map goo) xs } @-}
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
