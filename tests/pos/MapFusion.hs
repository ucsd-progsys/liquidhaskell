{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--exact-data-cons" @-}

{-@ LIQUID "--automatic-instances=liquidinstances" @-}

{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE FlexibleContexts    #-}


module MapFusion where

import Prelude hiding (map)

import Language.Haskell.Liquid.ProofCombinators

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f3 g3 x3 = f3 (g3 x3)

{-@ reflect map @-}
map :: (a -> b) -> L a -> L b
map f4 N = N
map f5 (C z zs) = C (f5 z) (map f5 zs)


{-@ map_fusion :: foo:(a -> a) -> goo:(a -> a) -> xoos:{L a | true }
               -> {map (compose foo goo) xoos == compose (map foo) (map goo) xoos } @-}
map_fusion :: (a -> a) -> (a -> a) -> L a -> Proof
map_fusion f1 g1 N        = trivial
map_fusion f2 g2 (C x xs) = map_fusion f2 g2 xs


data L a = N | C a (L a)
{-@ data L [llen] a = N | C {headlist :: a, taillist :: L a }@-}

{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen N        = 0
llen (C _ as) = 1 + llen as
