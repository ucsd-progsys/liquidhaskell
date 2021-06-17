{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE FlexibleContexts    #-}


module MapFusion where

import Prelude hiding (map, (++))

import Language.Haskell.Liquid.ProofCombinators

{-@ infixr ++ @-}

{-@ axiomatize ++ @-}
(++) :: L a -> L a -> L a
N ++ ys = ys 
(C x xs) ++ ys = C x (xs ++ ys)


{-@ associative :: xs:L a -> ys:L a -> zs:L a
                -> {(xs ++ ys) ++ zs == xs ++ (ys ++ zs)} @-}
associative :: L a -> L a -> L a -> Proof
associative N ys zs
  = trivial 

associative (C x xs) ys zs
  = associative xs ys zs



data L a = N | C a (L a)
{-@ data L [llen] a = N | C {headlist :: a, taillist :: L a }@-}



{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen N        = 0
llen (C _ xs) = 1 + llen xs

